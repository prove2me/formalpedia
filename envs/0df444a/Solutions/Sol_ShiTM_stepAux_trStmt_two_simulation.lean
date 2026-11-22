-- Prove2me | solution 1 for ShiTM.stepAux_trStmt_two_simulation
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-14T20:54:46.658735+00:00
-- url     : https://prove2.me/submissions/75558e16-1796-4ede-9260-0649303d1a9c

import Definitions.Def_ShiTM2_Composite

set_option autoImplicit false

open Turing.TM2 ShiTM2

/-!
# Step-exact simulation of the second component inside the composite machine

This file is the mirror of the first-component simulation lemma
(`ShiTM.stepAux_trStmt_one_simulation`): it proves that the SECOND embedded component of the
sequential composite `ShiTM2.comp` runs, *step for step*, as it does on its own.  Everything
here is about `ShiTM2.trStmt₂`, `ShiTM2.liftStk₂` and `ShiTM2.liftCfg₂` of
`Definitions/Def_ShiTM2_Composite.lean`.

## Why a step-exact statement, and not `Turing.Respects`

Mathlib's simulation infrastructure (`Turing.Respects`, `tr_respects`, `tr_eval`) tracks the
domain and the value of a computation but **not the step count**, and the step count is the
entire content of `Turing.TM2ComputableInPolyTime`.  So what is needed is an equation between
single applications of `Turing.TM2.stepAux`, which is what is proved below.  Note that
`stepAux` recurses the *whole* `Stmt` tree inside one `Turing.TM2.step`
(`Mathlib/Computability/TuringMachine/StackTuringMachine.lean:161-168`), so one `stepAux`
equation is exactly one machine step.

## No halt asymmetry: the label law is uniform

For the first component the translation must rewrite `Stmt.halt` to
`Stmt.goto (fun _ => lcopyA)`, because `Turing.TM2.step M ⟨none, _, _⟩ = none`
(ibid. `:170-172`) makes a halted `TM2` dead and unresumable, and the composite still has work
to do.  Nothing of the kind happens here: `ShiTM2.trStmt₂` sends `Stmt.halt` to `Stmt.halt`,
since when the second component halts the composite halts.  Correspondingly `ShiTM2.liftCfg₂`
carries the label through with `Option.map (injΛ₂ tm₁ tm₂)` where `ShiTM2.liftCfg₁` had to use
`Option.elim`.

That is the one real difference from the first-component lemma, and it *collapses* what were
two separate label conjuncts there into the single uniform law

`(stepAux (trStmt₂ tm₁ tm₂ q) w (liftStk₂ tm₁ tm₂ T S)).l
    = ((stepAux q w.2.1 S).l).map (injΛ₂ tm₁ tm₂)`,

which covers the `goto` leaf by `Option.map_some` (core `Init/Data/Option/Basic.lean:58`) and
the `halt` leaf by `Option.map_none` (ibid. `:57`) at once.  Both of those are `rfl`.

## Shape of the conclusion

Conjunct 1 is the single configuration equation
`stepAux (trStmt₂ q) w (liftStk₂ T S) = liftCfg₂ T w.1 w.2.2 (stepAux q w.2.1 S)`.
Because the right-hand side is again a `liftCfg₂`/`liftStk₂` of the component's own resulting
configuration, this one equation already says that

* the second component's stacks change exactly as they do in the component's own run;
* the background stacks `T` (the first machine's stacks and the scratch stack) are
  **untouched**;
* the first state component and the one-symbol transfer register are **unchanged**;
* the label is `injΛ₂` of the component's label, `none` staying `none`.

Conjunct 2 spells the state and stack halves out without unfolding `liftCfg₂`, and conjunct 3
is the label law above.

`ShiTM2.prjσ₂`, `ShiTM2.injσ₂`, `ShiTM2.prjσ₁` are `abbrev`s for `s.2.1`, `(s.1, u, s.2.2)`,
`s.1`; the statement is written with the raw projections, so it can be read with or without
them.

## Lemmas used, all checked at revision 0df444a360eaa60ab8c11dca51a86af692955474

* `Function.rec_update` -- `Mathlib/Logic/Function/Basic.lean:745`
* `Function.update` -- `Mathlib/Logic/Function/Basic.lean:638`
* `Sum.inl_injective` -- `Mathlib/Data/Sum/Basic.lean:41`
* `Sum.inr_injective` -- `Mathlib/Data/Sum/Basic.lean:43`
* `Turing.TM2.stepAux` -- `Mathlib/Computability/TuringMachine/StackTuringMachine.lean:161`.
  Applications of `stepAux` to a `Stmt` constructor are reduced here **definitionally**
  (`rfl`), not through the `stepAux.eq_1 .. eq_7` simp lemmas (ibid. `:175-176`), which do not
  fire on the composite side.  This is the idiom Mathlib itself uses: `Turing.TM2.step_run`
  (ibid. `:490-494`) proves exactly such an equation, `Function.update` in the stack argument
  and all, by a bare `rfl`; see also `unfold stepAux` at ibid. `:275` and
  `simp only [TM2.stepAux]` in `Mathlib/Computability/TuringMachine/ToPartrec.lean:594,624,789`
* `Turing.TM2.Cfg` -- ibid. `:144`
* `Bool.eq_false_or_eq_true` -- core `Init/Data/Bool.lean:59`
* `cond_true`, `cond_false` -- core `Init/SimpLemmas.lean:411-412`
* `Option.map_none`, `Option.map_some` -- core `Init/Data/Option/Basic.lean:57-58`
-/

/-- The lift hits the second machine's stacks on the nose.  True by `rfl`: `injK₂` is
`Sum.inr ∘ Sum.inl` and `liftStk₂` is a `match`. -/
private theorem shiSimB_liftStk₂_apply (tm₁ tm₂ : Turing.FinTM2)
    (T : ∀ k, List (CompΓ tm₁ tm₂ k)) (S : ∀ i, List (tm₂.Γ i)) (i : tm₂.K) :
    liftStk₂ tm₁ tm₂ T S (injK₂ tm₁ tm₂ i) = S i := by
  first
  | (rfl
     done)
  | (simp only [liftStk₂]
     done)

/-- `injK₂` is injective; it is `Sum.inr ∘ Sum.inl`. -/
private theorem shiSimB_injK₂_inj (tm₁ tm₂ : Turing.FinTM2) :
    Function.Injective (injK₂ tm₁ tm₂) := by
  intro a b h
  first
  | (exact Sum.inl.inj (Sum.inr.inj h)
     done)
  | (exact Sum.inl_injective (Sum.inr_injective h)
     done)
  | (injection h with h1
     injection h1
     done)
  | (injection h
     done)

/-- **The key commutation, on the concrete lift.**  Updating the *lifted* stack family at an
index in the image of `injK₂` is the same as lifting the family updated at the preimage index.

This is the one place where a dependent `Function.update` has to be pushed through an injection
into a dependent codomain, and it is exactly what `Function.rec_update`
(`Mathlib/Logic/Function/Basic.lean:745`) was written for: its `recursor` argument has type
`((i : ι) → α (ctor i)) → ((i : κ) → α i)`, which is *literally* the type of
`liftStk₂ tm₁ tm₂ T`, because the composite alphabet `CompΓ` is an iterated `Sum.elim` and
hence its restriction along `injK₂ = Sum.inr ∘ Sum.inl` is `tm₂.Γ` by `rfl`.  No `dite`, no
`Eq.ndrec`, no `Equiv`, no `List.map` and no cast occurs.

The implicit family `α` is pinned by name, because
`?α (Sum.inr (Sum.inl i)) =?= List (CompΓ tm₁ tm₂ (injK₂ tm₁ tm₂ i))` is not a Miller pattern
and higher-order unification will not solve it.  The value `x` is typed at the *composite*
alphabet `List (CompΓ tm₁ tm₂ (injK₂ tm₁ tm₂ i))` rather than at `List (tm₂.Γ i)`: the two are
defeq, but `rw` matches syntactically and the composite spelling is the one that appears in the
goal.

The off-image obligation `hoff` has two arms, not one: `Sum.inl i'`, the first machine's stacks,
and `Sum.inr (Sum.inr u)`, the scratch stack, whose `u : Unit` must be destructed. -/
private theorem shiSimB_update_liftStk₂ (tm₁ tm₂ : Turing.FinTM2) [DecidableEq tm₂.K]
    [DecidableEq (CompK tm₁ tm₂)] (T : ∀ k, List (CompΓ tm₁ tm₂ k))
    (S : ∀ i, List (tm₂.Γ i)) (i : tm₂.K)
    (x : List (CompΓ tm₁ tm₂ (injK₂ tm₁ tm₂ i))) :
    Function.update (liftStk₂ tm₁ tm₂ T S) (injK₂ tm₁ tm₂ i) x
      = liftStk₂ tm₁ tm₂ T (Function.update S i x) := by
  have hmem : ∀ (f : ∀ j : tm₂.K, List (CompΓ tm₁ tm₂ (injK₂ tm₁ tm₂ j))) (j : tm₂.K),
      liftStk₂ tm₁ tm₂ T f (injK₂ tm₁ tm₂ j) = f j := by
    intro f j
    first
    | (rfl
       done)
    | (simp only [liftStk₂]
       done)
  have hoff : ∀ (f₁ f₂ : ∀ j : tm₂.K, List (CompΓ tm₁ tm₂ (injK₂ tm₁ tm₂ j)))
      (k : CompK tm₁ tm₂), (∀ j, injK₂ tm₁ tm₂ j ≠ k) →
      liftStk₂ tm₁ tm₂ T f₁ k = liftStk₂ tm₁ tm₂ T f₂ k := by
    intro f₁ f₂ k hk
    rcases k with i' | j' | u
    · first
      | (rfl
         done)
      | (simp only [liftStk₂]
         done)
    · exact (hk j' rfl).elim
    · first
      | (rfl
         done)
      | (cases u
         rfl
         done)
      | (obtain ⟨⟩ := u
         rfl
         done)
  exact (Function.rec_update (α := fun k : CompK tm₁ tm₂ => List (CompΓ tm₁ tm₂ k))
    (shiSimB_injK₂_inj tm₁ tm₂) (liftStk₂ tm₁ tm₂ T) hmem hoff S i x).symm

/-- **The single-`stepAux` simulation for the second component, as one configuration
equation.**  Proved by induction on the statement; all seven `Stmt` constructors.

Each case reduces both sides with a pair of `rfl`-`have`s (`e1` on the component's own
`stepAux`, `e2` on the composite's) and then, in the `push` and `pop` cases only, rewrites with
`shiSimB_update_liftStk₂` -- the one step that is *not* definitional, since `Function.update` of
a lift and the lift of a `Function.update` differ by a `dite` on the stack index.  `peek`,
`load`, `goto` and `halt` need no rewriting at all: they close by `exact`/`rfl` on definitional
reduction, the last two because `Option.map` on a constructor reduces by iota. -/
private theorem shiSimB_stepAux_lift₂ (tm₁ tm₂ : Turing.FinTM2) [DecidableEq tm₂.K]
    [DecidableEq (CompK tm₁ tm₂)] (T : ∀ k, List (CompΓ tm₁ tm₂ k)) :
    ∀ (q : Stmt tm₂.Γ tm₂.Λ tm₂.σ) (w : Compσ tm₁ tm₂) (S : ∀ i, List (tm₂.Γ i)),
      stepAux (trStmt₂ tm₁ tm₂ q) w (liftStk₂ tm₁ tm₂ T S)
        = ({ l := ((stepAux q w.2.1 S).l).map (injΛ₂ tm₁ tm₂),
             var := (w.1, (stepAux q w.2.1 S).var, w.2.2),
             stk := liftStk₂ tm₁ tm₂ T (stepAux q w.2.1 S).stk } : CompCfg tm₁ tm₂) := by
  intro q
  induction q with
  | push i f q ih =>
    intro w S
    first
    | (have e1 : stepAux (Stmt.push i f q) w.2.1 S
             = stepAux q w.2.1 (Function.update S i (f w.2.1 :: S i)) := rfl
       have e2 : stepAux (trStmt₂ tm₁ tm₂ (Stmt.push i f q)) w (liftStk₂ tm₁ tm₂ T S)
             = stepAux (trStmt₂ tm₁ tm₂ q) w
                 (Function.update (liftStk₂ tm₁ tm₂ T S) (injK₂ tm₁ tm₂ i)
                   (f w.2.1 :: S i)) := rfl
       rw [e1, e2, shiSimB_update_liftStk₂]
       exact ih w (Function.update S i (f w.2.1 :: S i))
       done)
    | (simp only [trStmt₂, Turing.TM2.stepAux, prjσ₂, shiSimB_liftStk₂_apply,
         shiSimB_update_liftStk₂]
       exact ih w (Function.update S i (f w.2.1 :: S i))
       done)
    | (simp only [trStmt₂, Turing.TM2.stepAux, prjσ₂, shiSimB_liftStk₂_apply,
         shiSimB_update_liftStk₂]
       apply ih
       done)
  | peek i f q ih =>
    intro w S
    first
    | (exact ih (w.1, f w.2.1 (S i).head?, w.2.2) S
       done)
    | (have e1 : stepAux (Stmt.peek i f q) w.2.1 S
             = stepAux q (f w.2.1 (S i).head?) S := rfl
       have e2 : stepAux (trStmt₂ tm₁ tm₂ (Stmt.peek i f q)) w (liftStk₂ tm₁ tm₂ T S)
             = stepAux (trStmt₂ tm₁ tm₂ q) (w.1, f w.2.1 (S i).head?, w.2.2)
                 (liftStk₂ tm₁ tm₂ T S) := rfl
       rw [e1, e2]
       exact ih (w.1, f w.2.1 (S i).head?, w.2.2) S
       done)
    | (simp only [trStmt₂, Turing.TM2.stepAux, prjσ₂, injσ₂, shiSimB_liftStk₂_apply]
       exact ih (w.1, f w.2.1 (S i).head?, w.2.2) S
       done)
    | (simp only [trStmt₂, Turing.TM2.stepAux, prjσ₂, injσ₂, shiSimB_liftStk₂_apply]
       apply ih
       done)
  | pop i f q ih =>
    intro w S
    first
    | (have e1 : stepAux (Stmt.pop i f q) w.2.1 S
             = stepAux q (f w.2.1 (S i).head?) (Function.update S i (S i).tail) := rfl
       have e2 : stepAux (trStmt₂ tm₁ tm₂ (Stmt.pop i f q)) w (liftStk₂ tm₁ tm₂ T S)
             = stepAux (trStmt₂ tm₁ tm₂ q) (w.1, f w.2.1 (S i).head?, w.2.2)
                 (Function.update (liftStk₂ tm₁ tm₂ T S) (injK₂ tm₁ tm₂ i)
                   (S i).tail) := rfl
       rw [e1, e2, shiSimB_update_liftStk₂]
       exact ih (w.1, f w.2.1 (S i).head?, w.2.2) (Function.update S i (S i).tail)
       done)
    | (simp only [trStmt₂, Turing.TM2.stepAux, prjσ₂, injσ₂, shiSimB_liftStk₂_apply,
         shiSimB_update_liftStk₂]
       exact ih (w.1, f w.2.1 (S i).head?, w.2.2) (Function.update S i (S i).tail)
       done)
    | (simp only [trStmt₂, Turing.TM2.stepAux, prjσ₂, injσ₂, shiSimB_liftStk₂_apply,
         shiSimB_update_liftStk₂]
       apply ih
       done)
  | load a q ih =>
    intro w S
    first
    | (exact ih (w.1, a w.2.1, w.2.2) S
       done)
    | (have e1 : stepAux (Stmt.load a q) w.2.1 S = stepAux q (a w.2.1) S := rfl
       have e2 : stepAux (trStmt₂ tm₁ tm₂ (Stmt.load a q)) w (liftStk₂ tm₁ tm₂ T S)
             = stepAux (trStmt₂ tm₁ tm₂ q) (w.1, a w.2.1, w.2.2)
                 (liftStk₂ tm₁ tm₂ T S) := rfl
       rw [e1, e2]
       exact ih (w.1, a w.2.1, w.2.2) S
       done)
    | (simp only [trStmt₂, Turing.TM2.stepAux, prjσ₂, injσ₂]
       exact ih (w.1, a w.2.1, w.2.2) S
       done)
    | (simp only [trStmt₂, Turing.TM2.stepAux, prjσ₂, injσ₂]
       apply ih
       done)
  | branch c q₁ q₂ ih₁ ih₂ =>
    intro w S
    first
    | (have e1 : stepAux (Stmt.branch c q₁ q₂) w.2.1 S
             = cond (c w.2.1) (stepAux q₁ w.2.1 S) (stepAux q₂ w.2.1 S) := rfl
       have e2 : stepAux (trStmt₂ tm₁ tm₂ (Stmt.branch c q₁ q₂)) w (liftStk₂ tm₁ tm₂ T S)
             = cond (c w.2.1) (stepAux (trStmt₂ tm₁ tm₂ q₁) w (liftStk₂ tm₁ tm₂ T S))
                 (stepAux (trStmt₂ tm₁ tm₂ q₂) w (liftStk₂ tm₁ tm₂ T S)) := rfl
       rw [e1, e2]
       rcases Bool.eq_false_or_eq_true (c w.2.1) with hc | hc <;>
         first
         | (simp only [hc, cond_true]
            exact ih₁ w S
            done)
         | (simp only [hc, cond_false]
            exact ih₂ w S
            done)
       done)
    | (simp only [trStmt₂, Turing.TM2.stepAux, prjσ₂]
       rcases Bool.eq_false_or_eq_true (c w.2.1) with hc | hc <;>
         first
         | (simp only [hc, cond_true]
            exact ih₁ w S
            done)
         | (simp only [hc, cond_false]
            exact ih₂ w S
            done)
       done)
  | goto g =>
    intro w S
    first
    | (rfl
       done)
    | (simp only [trStmt₂, Turing.TM2.stepAux, prjσ₂, Option.map_some]
       done)
    | (simp only [trStmt₂, Turing.TM2.stepAux, prjσ₂, Option.map_some]
       rfl
       done)
    | (simp [trStmt₂, Turing.TM2.stepAux, prjσ₂]
       done)
  | halt =>
    intro w S
    first
    | (rfl
       done)
    | (simp only [trStmt₂, Turing.TM2.stepAux, Option.map_none]
       done)
    | (simp only [trStmt₂, Turing.TM2.stepAux, Option.map_none]
       rfl
       done)
    | (simp [trStmt₂, Turing.TM2.stepAux]
       done)

/-- **Step-exact simulation of the second component of the sequential composite.**

Fix `tm₁ tm₂ : Turing.FinTM2` and a family `T` of background stacks of the composite (the first
machine's stacks and the scratch stack).  For every statement `q` of the second machine, every
composite internal state `w : tm₁.σ × tm₂.σ × Option (tm₂.Γ tm₂.k₀)` and every stack family `S`
of the second machine:

1. one `Turing.TM2.stepAux` of the translated statement `ShiTM2.trStmt₂ tm₁ tm₂ q`, run on the
   lifted stacks `ShiTM2.liftStk₂ tm₁ tm₂ T S`, is the `ShiTM2.liftCfg₂`-lift of one `stepAux`
   of `q` run on `S`.  In particular the second machine's stacks change exactly as they do in
   its own run, the background stacks `T` are untouched, and the first state component `w.1`
   and the transfer register `w.2.2` are unchanged;
2. the same, with the state and stack components spelled out, so that the statement can be used
   without unfolding `ShiTM2.liftCfg₂`;
3. the label of the translated run is `Option.map (ShiTM2.injΛ₂ tm₁ tm₂)` of the label of the
   original run -- a plain relabelling, with **no exception**.

Conjunct 3 is where this lemma differs from its first-component counterpart
`ShiTM.stepAux_trStmt_one_simulation`, and it differs by being *simpler*.  There, `Stmt.halt`
had to be rewritten to `Stmt.goto (fun _ => lcopyA)`, because `Turing.TM2.step ⟨none, _, _⟩`
is `none` and the composite must still perform the transfer and run the second machine; so the
label law split into a `some l ↦ some (injΛ₁ l)` case and a `none ↦ some (lcopyA)` case.  Here
`ShiTM2.trStmt₂` leaves `Stmt.halt` alone -- when the second component halts, the composite
halts -- so the two cases merge: `Option.map` sends `none` to `none` and `some l` to
`some (injΛ₂ l)`, and one unconditional equation covers the `goto` leaf and the `halt` leaf
together.

As there, conjunct 3 speaks of the leaf actually *reached*, not of the top constructor of `q`,
because `stepAux` recurses the entire `Stmt` tree inside a single `Turing.TM2.step`; so, e.g.,
`Stmt.push k f Stmt.halt` halts the composite in one step.

The two `DecidableEq` binders are needed because the `kDecidableEq` field of `Turing.FinTM2` is
a structure field, not an instance; `tm₂.kDecidableEq` and `ShiTM2.compKDecEq tm₁ tm₂` are the
intended arguments. -/
theorem solution (tm₁ tm₂ : Turing.FinTM2) [DecidableEq tm₂.K]
    [DecidableEq (CompK tm₁ tm₂)] (T : ∀ k, List (CompΓ tm₁ tm₂ k)) :
    (∀ (q : Stmt tm₂.Γ tm₂.Λ tm₂.σ) (w : Compσ tm₁ tm₂) (S : ∀ i, List (tm₂.Γ i)),
        stepAux (trStmt₂ tm₁ tm₂ q) w (liftStk₂ tm₁ tm₂ T S)
          = liftCfg₂ tm₁ tm₂ T w.1 w.2.2 (stepAux q w.2.1 S))
  ∧ (∀ (q : Stmt tm₂.Γ tm₂.Λ tm₂.σ) (w : Compσ tm₁ tm₂) (S : ∀ i, List (tm₂.Γ i)),
        (stepAux (trStmt₂ tm₁ tm₂ q) w (liftStk₂ tm₁ tm₂ T S)).var
            = (w.1, (stepAux q w.2.1 S).var, w.2.2)
      ∧ (stepAux (trStmt₂ tm₁ tm₂ q) w (liftStk₂ tm₁ tm₂ T S)).stk
            = liftStk₂ tm₁ tm₂ T (stepAux q w.2.1 S).stk)
  ∧ (∀ (q : Stmt tm₂.Γ tm₂.Λ tm₂.σ) (w : Compσ tm₁ tm₂) (S : ∀ i, List (tm₂.Γ i)),
        (stepAux (trStmt₂ tm₁ tm₂ q) w (liftStk₂ tm₁ tm₂ T S)).l
          = ((stepAux q w.2.1 S).l).map (injΛ₂ tm₁ tm₂)) := by
  have H := shiSimB_stepAux_lift₂ tm₁ tm₂ T
  refine ⟨fun q w S => ?_, fun q w S => ⟨?_, ?_⟩, fun q w S => ?_⟩
  · first
    | (exact H q w S
       done)
    | (rw [H q w S]
       done)
    | (rw [H q w S]
       rfl
       done)
    | (simp only [H q w S, liftCfg₂]
       done)
  · first
    | (rw [H q w S]
       done)
    | (rw [H q w S]
       rfl
       done)
    | (simp only [H q w S]
       done)
  · first
    | (rw [H q w S]
       done)
    | (rw [H q w S]
       rfl
       done)
    | (simp only [H q w S]
       done)
  · first
    | (rw [H q w S]
       done)
    | (rw [H q w S]
       rfl
       done)
    | (simp only [H q w S]
       done)
