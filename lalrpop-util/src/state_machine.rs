#![allow(dead_code)]

use std::fmt::Debug;

const DEBUG_ENABLED: bool = false;

macro_rules! debug {
    ($($args:expr),*) => {
        if DEBUG_ENABLED {
            eprintln!($($args),*);
        }
    }
}

pub trait ParserDefinition {
    type Location: Clone + Debug;
    type Error;
    type Token: Clone + Debug;
    type Symbol;
    type Success;

    fn start_location(&self) -> Self::Location;
    fn token_to_integer(&self, token: &Self::Token) -> Option<usize>;
    fn action(&self, state: i32, integer: usize) -> i32;
    fn error_action(&self, state: i32) -> i32;
    fn eof_action(&self, state: i32) -> i32;
    fn goto(&self, state: i32, nt: i32) -> i32;
    fn token_to_symbol(&self, token: Self::Token) -> Self::Symbol;
    fn expected_tokens(&self, state: i32) -> Vec<String>;
    fn uses_error_recovery(&self) -> bool;
    fn error_recovery_symbol(&self, recovery: ErrorRecovery<Self>) -> Self::Symbol;
    fn reduce(
        &self,
        action: i32,
        start_location: Option<&Self::Location>,
        states: &mut Vec<i32>,
        symbols: &mut Vec<SymbolTriple<Self>>,
    ) -> Option<ParseResult<Self>>;
    fn simulate_reduce(&self, action: i32) -> SimulatedReduce;
}

pub struct SimulatedReduce {
    states_to_pop: usize,
    nonterminal_produced: i32,
}

// These aliases are an elaborate hack to get around
// the warnings when you define a type alias like `type Foo<D: Trait>`
#[doc(hidden)]
pub type Location<D> = <D as ParserDefinition>::Location;
#[doc(hidden)]
pub type Token<D> = <D as ParserDefinition>::Token;
#[doc(hidden)]
pub type Error<D> = <D as ParserDefinition>::Error;
#[doc(hidden)]
pub type Success<D> = <D as ParserDefinition>::Success;
#[doc(hidden)]
pub type Symbol<D> = <D as ParserDefinition>::Symbol;

pub type ParseError<D> = ::ParseError<Location<D>, Token<D>, Error<D>>;
pub type ParseResult<D> = Result<Success<D>, ParseError<D>>;
pub type TokenTriple<D> = (Location<D>, Token<D>, Location<D>);
pub type SymbolTriple<D> = (Location<D>, Symbol<D>, Location<D>);
pub type ErrorRecovery<D> = ::ErrorRecovery<Location<D>, Token<D>, Error<D>>;

pub struct Parser<D, I>
where
    D: ParserDefinition,
    I: Iterator<Item = Result<TokenTriple<D>, ParseError<D>>>,
{
    definition: D,
    tokens: I,
    states: Vec<i32>,
    symbols: Vec<SymbolTriple<D>>,
    last_location: D::Location,
}

enum NextToken<D: ParserDefinition> {
    FoundToken(TokenTriple<D>, usize),
    EOF,
    Done(ParseResult<D>),
}

impl<D, I> Parser<D, I>
where
    D: ParserDefinition,
    I: Iterator<Item = Result<TokenTriple<D>, ParseError<D>>>,
{
    fn top_state(&self) -> i32 {
        *self.states.last().unwrap()
    }

    fn parse(&mut self) -> ParseResult<D> {
        // Outer loop: each time we continue around this loop, we
        // shift a new token from the input. We break from the loop
        // when the end of the input is reached (we return early if an
        // error occurs).
        'shift: loop {
            let (mut lookahead, mut integer) = match self.next_token() {
                NextToken::FoundToken(l, i) => (l, i),
                NextToken::EOF => return self.parse_eof(),
                NextToken::Done(e) => return e,
            };

            debug!("SHIFT: {:?}", lookahead);

            debug!("integer: {:?}", integer);

            'inner: loop {
                let top_state = self.top_state();
                let action = self.definition.action(top_state, integer);

                if action > 0 {
                    // Shift and transition to state `action - 1`
                    let symbol = self.definition.token_to_symbol(lookahead.1);
                    self.states.push(action - 1);
                    self.symbols.push((lookahead.0, symbol, lookahead.2));
                    continue 'shift;
                } else if action < 0 {
                    if let Some(r) = self.definition.reduce(
                        action,
                        Some(&lookahead.0),
                        &mut self.states,
                        &mut self.symbols,
                    ) {
                        return match r {
                            // we reached eof, but still have lookahead
                            Ok(_) => Err(::ParseError::ExtraToken { token: lookahead }),
                            Err(e) => Err(e),
                        };
                    }
                } else {
                    if !self.definition.uses_error_recovery() {
                        return Err(self.unrecognized_token_error(
                            Some(lookahead),
                            self.top_state(),
                        ));
                    } else {
                        match self.error_recovery(Some(lookahead), Some(integer)) {
                            NextToken::FoundToken(l, i) => {
                                lookahead = l;
                                integer = i;
                                continue 'inner;
                            }
                            NextToken::EOF => return self.parse_eof(),
                            NextToken::Done(e) => return e,
                        }
                    }
                }
            }
        }
    }

    /// Invoked when we have no more tokens to consume.
    fn parse_eof(&mut self) -> ParseResult<D> {
        loop {
            let top_state = self.top_state();
            let action = self.definition.eof_action(top_state);
            if action < 0 {
                if let Some(r) =
                    self.definition
                        .reduce(action, None, &mut self.states, &mut self.symbols)
                {
                    return r;
                }
            } else {
                match self.error_recovery(None, None) {
                    NextToken::FoundToken(..) => panic!("cannot find token at EOF"),
                    NextToken::Done(e) => return e,
                    NextToken::EOF => continue,
                }
            }
        }
    }

    fn error_recovery(
        &mut self,
        mut opt_lookahead: Option<TokenTriple<D>>,
        mut opt_integer: Option<usize>,
    ) -> NextToken<D> {
        let error = self.unrecognized_token_error(opt_lookahead.clone(), self.top_state());

        let mut dropped_tokens = vec![];

        // We are going to insert ERROR into the lookahead. So, first,
        // perform all reductions from current state triggered by having
        // ERROR in the lookahead.
        loop {
            let state = self.top_state();
            let action = self.definition.error_action(state);
            if action >= 0 {
                break;
            }

            if let Some(r) = self.reduce(action, opt_lookahead.as_ref().map(|l| &l.0)) {
                return NextToken::Done(r);
            }
        }

        // Now try to find the recovery state.
        let states_len = self.states.len();
        let top = 'find_state: loop {
            // Go backwards through the states...
            for top in (0..states_len).rev() {
                let state = self.states[top];
                // ...fetch action for error token...
                let action = self.definition.error_action(state);
                // ...if action is error or reduce, go to next state...
                if action <= 0 {
                    continue;
                }
                // ...otherwise, action *must* be shift. That would take us into `error_state`.
                let error_state = action - 1;
                // If `error_state` can accept this lookahead, we are done.
                if self.accepts(error_state, &self.states[..top + 1], opt_integer) {
                    break 'find_state top;
                }
            }

            // Otherwise, if we couldn't find a state that would --
            // after shifting the error token -- accept the lookahead,
            // then drop the lookahead and advance to next token in
            // the input.
            match opt_lookahead.take() {
                // If the lookahead is EOF, we can't drop any more
                // tokens, abort error recovery and just report the
                // original error (it might be nice if we would
                // propagate back the dropped tokens, though).
                None => return NextToken::Done(Err(error)),

                // Else, drop the current token and shift to the
                // next. If there is a next token, we will `continue`
                // to the start of the `'find_state` loop.
                Some(lookahead) => {
                    dropped_tokens.push(lookahead);
                    match self.next_token() {
                        NextToken::FoundToken(next_lookahead, next_integer) => {
                            opt_lookahead = Some(next_lookahead);
                            opt_integer = Some(next_integer);
                        }
                        NextToken::EOF => {
                            opt_lookahead = None;
                            opt_integer = None;
                        }
                        NextToken::Done(e) => return NextToken::Done(e),
                    }
                }
            }
        };

        // If we get here, we are ready to push the error recovery state.

        // We have to compute the span for the error recovery
        // token. We do this first, before we pop any symbols off the
        // stack. There are several possibilities, in order of
        // preference.
        //
        // For the **start** of the message, we prefer to use the start of any
        // popped states. This represents parts of the input we had consumed but
        // had to roll back and ignore.
        //
        // Example:
        //
        //       a + (b + /)
        //              ^ start point is here, since this `+` will be popped off
        //
        // If there are no popped states, but there *are* dropped tokens, we can use
        // the start of those.
        //
        // Example:
        //
        //       a + (b + c e)
        //                  ^ start point would be here
        //
        // Finally, if there are no popped states *nor* dropped tokens, we can use
        // the end of the top-most state.

        let start = if let Some(popped_sym) = self.symbols.get(top) {
            popped_sym.0.clone()
        } else if let Some(dropped_token) = dropped_tokens.first() {
            dropped_token.0.clone()
        } else if top > 0 {
            self.symbols[top - 1].2.clone()
        } else {
            self.definition.start_location()
        };

        // For the end span, here are the possibilities:
        //
        // We prefer to use the end of the last dropped token.
        //
        // Examples:
        //
        //       a + (b + /)
        //              ---
        //       a + (b c)
        //              -
        //
        // But, if there are no dropped tokens, we will use the end of the popped states,
        // if any:
        //
        //       a + /
        //         -
        //
        // If there are neither dropped tokens *or* popped states,
        // then the user is simulating insertion of an operator. In
        // this case, we prefer the start of the lookahead, but
        // fallback to the start if we are at EOF.
        //
        // Examples:
        //
        //       a + (b c)
        //             -

        let end = if let Some(dropped_token) = dropped_tokens.last() {
            dropped_token.2.clone()
        } else if states_len - 1 > top {
            self.symbols.last().unwrap().2.clone()
        } else if let Some(lookahead) = opt_lookahead.as_ref() {
            lookahead.0.clone()
        } else {
            start.clone()
        };

        self.states.truncate(top + 1);
        self.symbols.truncate(top);

        let recover_state = self.states[top];
        let error_action = self.definition.error_action(recover_state);
        let error_state = error_action - 1;
        self.states.push(error_state);
        let recovery = self.definition.error_recovery_symbol(::ErrorRecovery {
            error: error,
            dropped_tokens: dropped_tokens,
        });
        self.symbols.push((start, recovery, end));

        match (opt_lookahead, opt_integer) {
            (Some(l), Some(i)) => NextToken::FoundToken(l, i),
            (None, None) => NextToken::EOF,
            (l, i) => panic!("lookahead and integer mismatched: {:?}, {:?}", l, i),
        }
    }

    /// The `accepts` function has the job of figuring out whether the
    /// given error state would "accept" the given lookahead. We
    /// basically trace through the LR automaton looking for one of
    /// two outcomes:
    ///
    /// - the lookahead is eventually shifted
    /// - we reduce to the end state successfully (in the case of EOF).
    ///
    /// If we used the pure LR(1) algorithm, we wouldn't need this
    /// function, because we would be guaranteed to error immediately
    /// (and not after some number of reductions). But with an LALR
    /// (or Lane Table) generated automaton, it is possible to reduce
    /// some number of times before encountering an error. Failing to
    /// take this into account can lead error recovery into an
    /// infinite loop (see the `error_recovery_lalr_loop` test) or
    /// produce crappy results (see `error_recovery_lock_in`).
    fn accepts(&self, error_state: i32, states: &[i32], opt_integer: Option<usize>) -> bool {
        let mut states = states.to_vec();
        states.push(error_state);
        loop {
            let mut states_len = states.len();
            let top = states[states_len - 1];
            let action = match opt_integer {
                None => self.definition.eof_action(top),
                Some(i) => self.definition.action(top, i),
            };

            // If we encounter an error action, we do **not** accept.
            if action == 0 {
                return false;
            }

            // If we encounter a shift action, we DO accept.
            if action > 0 {
                return true;
            }

            // If we encounter a reduce action, we need to simulate its
            // effect on the state stack.
            let SimulatedReduce {
                states_to_pop,
                nonterminal_produced,
            } = self.definition.simulate_reduce(-action);
            states_len -= states_to_pop;
            states.truncate(states_len);
            let top = states[states_len - 1];
            let next_state = self.definition.goto(top, nonterminal_produced);
            states.push(next_state);
        }
    }

    fn reduce(
        &mut self,
        action: i32,
        lookahead_start: Option<&D::Location>,
    ) -> Option<ParseResult<D>> {
        self.definition
            .reduce(action, lookahead_start, &mut self.states, &mut self.symbols)
    }

    fn unrecognized_token_error(
        &self,
        token: Option<TokenTriple<D>>,
        top_state: i32,
    ) -> ParseError<D> {
        ::ParseError::UnrecognizedToken {
            token: token,
            expected: self.definition.expected_tokens(top_state),
        }
    }

    /// Consume the next token from the input and classify it into a
    /// token index ("integer"). Classification can fail with an
    /// error. If there are no more tokens, signal EOF.
    fn next_token(&mut self) -> NextToken<D> {
        let token = match self.tokens.next() {
            Some(Ok(v)) => v,
            Some(Err(e)) => return NextToken::Done(Err(e)),
            None => return NextToken::EOF,
        };

        self.last_location = token.2.clone();

        let integer = match self.definition.token_to_integer(&token.1) {
            Some(i) => i,
            None => {
                return NextToken::Done(Err(self.unrecognized_token_error(
                    Some(token),
                    self.top_state(),
                )))
            }
        };

        NextToken::FoundToken(token, integer)
    }
}
