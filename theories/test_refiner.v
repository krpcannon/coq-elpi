From elpi Require Import elpi.

Elpi Init "./" "./elpi/".

Elpi Accumulate File "pervasives.elpi".
Elpi Accumulate File "coq-refiner.elpi".

Elpi Run "
  {{plus}} = const GR, coq-env-const GR B T,
  of B TY RB, coq-say RB, coq-say TY".

Elpi Run "
  {{plus_n_O}} = const GR, coq-env-const GR B T,
  of B TY RB, coq-say RB, coq-say TY".

Elpi Accumulate "
mode (is-grinded? i).
is-grinded? (?? as X) :- X = tt.

grind X hole :- grinded? G, is-grinded? G.
grind X X.
grind (app L) (app L1) :- map L grind L1.
grind (lam N T F) (lam N T1 F1) :-
  grind T T1, pi x\ grind (F x) (F1 x).
grind (prod N T F) (prod N T1 F1) :-
  grind T T1, pi x\ grind (F x) (F1 x).
grind (let N T B F) (let N T1 B1 F1) :-
  grind T T1, grind B B1, pi x\ grind (F x) (F1 x).
grind (fix N Rno Ty F) (fix N Rno Ty1 F1) :-
  grind Ty Ty1, pi x\ grind (F x) (F1 x).
grind (match T R B) (match T1 R1 B1) :-
  grind T T1, grind R R1, map B grind B1.

mode (is-tt i).
is-tt tt.

test-grind B Ty E :-
  $new_safe Errs,
  grinded? _ =>
  (grind B X ; Stop = tt),
  if (is-tt Stop) ($open_safe Errs E)
     (if (coq-say X, of X Ty _) fail (fail,$stash Errs x,fail)).

".

Elpi Run "
  {{plus_n_O}} = const GR, coq-env-const GR B Ty,
  test-grind B Ty E,
  coq-say E.
".