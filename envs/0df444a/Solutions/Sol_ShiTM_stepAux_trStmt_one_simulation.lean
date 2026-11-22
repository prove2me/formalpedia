-- Prove2me | solution 1 for ShiTM.stepAux_trStmt_one_simulation
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-14T19:38:24.989908+00:00
-- url     : https://prove2.me/submissions/3192aa17-1830-4376-9ba6-9c3a7c0074dd

import Definitions.Def_ShiTM2_Composite

set_option autoImplicit false

open Turing.TM2 ShiTM2

/-!
# Step-exact simulation of the first component inside the composite machine

This file proves the acknowledged bottleneck of the `TM2ComputableInPolyTime.comp`
programme: an embedded component machine's run lifts to the composite machine's run,
*step for step*.  Everything here is about the FIRST component, i.e. about
`ShiTM2.trStmt₁` and `ShiTM2.liftStk₁` of `Definitions/Def_ShiTM2_Composite.lean`.

## Why a step-exact statement, and not `Turing.Respects`

Mathlib's simulation infrastructure (`Turing.Respects`, `tr_respects`, `tr_eval`) tracks
the domain and the value of a computation but **not the step count**, and the step count
is the entire content of `TM2ComputableInPolyTime`.  So what is needed is an equation
between single applications of `Turing.TM2.stepAux`, which is what is proved below.
Note that `stepAux` recurses the *whole* `Stmt` tree inside one `Turing.TM2.step`
(`StackTuringMachine.lean:161-168`), so one `stepAux` equation is exactly one machine
step.

## The halt asymmetry

`Turing.TM2.step M ⟨none, _, _⟩ = none` (`StackTuringMachine.lean:170-172`): a halted
`TM2` is *dead* and cannot be resumed.  Therefore the first component's program cannot be
reused verbatim in a sequential composite; its `Stmt.halt` leaves must be rewritten, which
is what `ShiTM2.trStmt₁` does (`Stmt.halt ↦ Stmt.goto (fun _ => lcopyA)`).  Consequently
the simulation is **not** a plain relabelling: where the original run produces the label
`Option.none` and dies, the translated run produces `Option.some (lcopyA tm₁ tm₂)` and
stays live.  Conjuncts 3 and 4 of `solution` state the two label cases separately so that
this asymmetry is explicit; it is the whole purpose of the translation.

## Shape of the conclusion

Conjunct 1 is the single configuration equation
`stepAux (trStmt₁ q) w (liftStk₁ T S) = liftCfg₁ T w.2.1 w.2.2 (stepAux q w.1 S)`.
Because the right-hand side is again a `liftCfg₁`/`liftStk₁` of the component's own
resulting configuration, this one equation already says that

* the component's stacks change exactly as they do in the component's own run;
* the background stacks `T` (the second machine's stacks and the scratch stack) are
  **untouched**;
* the second state component and the one-symbol transfer register are **unchanged**;
* the label is `injΛ₁` of the component's label, save for the halt case.

Conjunct 2 spells the state and stack halves out without unfolding `liftCfg₁`.

`ShiTM2.prjσ₁`, `ShiTM2.injσ₁`, `ShiTM2.prjσ₂` are `abbrev`s for `w.1`, `(u, w.2)`,
`w.2.1`; the statement is written with the raw projections, so it can be read with or
without them.

## Lemmas used, all checked at revision 0df444a360eaa60ab8c11dca51a86af692955474

* `Function.rec_update` -- `Mathlib/Logic/Function/Basic.lean:745`
* `Function.update` -- `Mathlib/Logic/Function/Basic.lean:638`
* `Sum.inl_injective` -- `Mathlib/Data/Sum/Basic.lean:41`
* `Turing.TM2.stepAux` -- `Mathlib/Computability/TuringMachine/StackTuringMachine.lean:161`.
  Applications of `stepAux` to a `Stmt` constructor are reduced here **definitionally**
  (`rfl`), not through the `stepAux.eq_1 .. eq_7` simp lemmas (ibid. `:175-176`), which do
  not fire on the composite side.  This is the idiom Mathlib itself uses: `Turing.TM2.step_run`
  (ibid. `:490-494`) proves exactly such an equation, `update` in the stack argument and all,
  by `rfl`; see also `unfold stepAux` at ibid. `:275` and `simp only [TM2.stepAux]` in
  `Mathlib/Computability/TuringMachine/ToPartrec.lean:594,624,789`
* `Turing.TM2.Cfg` -- ibid. `:144`
* `Bool.eq_false_or_eq_true` -- core `Init/Data/Bool.lean:59`
* `cond_true`, `cond_false` -- core `Init/SimpLemmas.lean:411-412`
* `Option.elim_none`, `Option.elim_some` -- core `Init/Data/Option/Lemmas.lean:735,737`
-/

/-- The lift hits the first machine's stacks on the nose.  True by `rfl`: `injK₁` is
`Sum.inl` and `liftStk₁` is a `match`. -/
private theorem shiSim2_liftStk₁_apply (tm₁ tm₂ : Turing.FinTM2)
    (T : ∀ k, List (CompΓ tm₁ tm₂ k)) (S : ∀ i, List (tm₁.Γ i)) (i : tm₁.K) :
    liftStk₁ tm₁ tm₂ T S (injK₁ tm₁ tm₂ i) = S i := by
  first
  | (rfl
     done)
  | (simp only [liftStk₁]
     done)

/-- `injK₁` is injective; it is `Sum.inl`. -/
private theorem shiSim2_injK₁_inj (tm₁ tm₂ : Turing.FinTM2) :
    Function.Injective (injK₁ tm₁ tm₂) := by
  intro a b h
  first
  | (exact Sum.inl.inj h
     done)
  | (exact Sum.inl_injective h
     done)
  | (injection h
     done)

/-- **The key commutation, on the concrete lift.**  Updating the *lifted* stack family at
an index in the image of `injK₁` is the same as lifting the family updated at the
preimage index.

This is the one place where a dependent `Function.update` has to be pushed through an
injection into a dependent codomain, and it is exactly what `Function.rec_update`
(`Mathlib/Logic/Function/Basic.lean:745`) was written for: its `recursor` argument has
type `((i : ι) → α (ctor i)) → ((i : κ) → α i)`, which is *literally* the type of
`liftStk₁ tm₁ tm₂ T`, because the composite alphabet `CompΓ` is a `Sum.elim` and hence its
restriction along `injK₁ = Sum.inl` is `tm₁.Γ` by `rfl`.  No `dite`, no `Eq.ndrec`, no
`Equiv`, no `List.map` and no cast occurs.

A previous attempt characterised the lift by hypotheses (`L S (injK₁ i) = S i`) instead of
naming it; `rec_update` then left `?recursor` unsolved, since a hypothesised lift has no
constant head.  `liftStk₁` supplies the constant head. -/
private theorem shiSim2_update_liftStk₁ (tm₁ tm₂ : Turing.FinTM2) [DecidableEq tm₁.K]
    [DecidableEq (CompK tm₁ tm₂)] (T : ∀ k, List (CompΓ tm₁ tm₂ k))
    (S : ∀ i, List (tm₁.Γ i)) (i : tm₁.K)
    (x : List (CompΓ tm₁ tm₂ (injK₁ tm₁ tm₂ i))) :
    Function.update (liftStk₁ tm₁ tm₂ T S) (injK₁ tm₁ tm₂ i) x
      = liftStk₁ tm₁ tm₂ T (Function.update S i x) := by
  have hmem : ∀ (f : ∀ j : tm₁.K, List (CompΓ tm₁ tm₂ (injK₁ tm₁ tm₂ j))) (j : tm₁.K),
      liftStk₁ tm₁ tm₂ T f (injK₁ tm₁ tm₂ j) = f j := by
    intro f j
    first
    | (rfl
       done)
    | (simp only [liftStk₁]
       done)
  have hoff : ∀ (f₁ f₂ : ∀ j : tm₁.K, List (CompΓ tm₁ tm₂ (injK₁ tm₁ tm₂ j)))
      (k : CompK tm₁ tm₂), (∀ j, injK₁ tm₁ tm₂ j ≠ k) →
      liftStk₁ tm₁ tm₂ T f₁ k = liftStk₁ tm₁ tm₂ T f₂ k := by
    intro f₁ f₂ k hk
    rcases k with i' | j' | u
    · exact (hk i' rfl).elim
    · first
      | (rfl
         done)
      | (simp only [liftStk₁]
         done)
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
    (shiSim2_injK₁_inj tm₁ tm₂) (liftStk₁ tm₁ tm₂ T) hmem hoff S i x).symm

/-- **The single-`stepAux` simulation for the first component, as one configuration
equation.**  Proved by induction on the statement; all seven `Stmt` constructors.

Each case reduces both sides with a pair of `rfl`-`have`s (`e1` on the component's own
`stepAux`, `e2` on the composite's) and then, in the `push` and `pop` cases only, rewrites
with `shiSim2_update_liftStk₁` -- the one step that is *not* definitional, since
`Function.update` of a lift and the lift of a `Function.update` differ by a `dite` on the
stack index.  `peek`, `load`, `goto` and `halt` need no rewriting at all: they close by
`exact`/`rfl` on definitional reduction. -/
private theorem shiSim2_stepAux_lift₁ (tm₁ tm₂ : Turing.FinTM2) [DecidableEq tm₁.K]
    [DecidableEq (CompK tm₁ tm₂)] (T : ∀ k, List (CompΓ tm₁ tm₂ k)) :
    ∀ (q : Stmt tm₁.Γ tm₁.Λ tm₁.σ) (w : Compσ tm₁ tm₂) (S : ∀ i, List (tm₁.Γ i)),
      stepAux (trStmt₁ tm₁ tm₂ q) w (liftStk₁ tm₁ tm₂ T S)
        = ({ l := Option.some ((stepAux q w.1 S).l.elim (lcopyA tm₁ tm₂)
                                 (injΛ₁ tm₁ tm₂)),
             var := ((stepAux q w.1 S).var, w.2),
             stk := liftStk₁ tm₁ tm₂ T (stepAux q w.1 S).stk } : CompCfg tm₁ tm₂) := by
  intro q
  induction q with
  | push i f q ih =>
    intro w S
    first
    | (have e1 : stepAux (Stmt.push i f q) w.1 S
             = stepAux q w.1 (Function.update S i (f w.1 :: S i)) := rfl
       have e2 : stepAux (trStmt₁ tm₁ tm₂ (Stmt.push i f q)) w (liftStk₁ tm₁ tm₂ T S)
             = stepAux (trStmt₁ tm₁ tm₂ q) w
                 (Function.update (liftStk₁ tm₁ tm₂ T S) (injK₁ tm₁ tm₂ i)
                   (f w.1 :: S i)) := rfl
       rw [e1, e2, shiSim2_update_liftStk₁]
       exact ih w (Function.update S i (f w.1 :: S i))
       done)
    | (simp only [trStmt₁, Turing.TM2.stepAux, prjσ₁, shiSim2_liftStk₁_apply,
         shiSim2_update_liftStk₁]
       exact ih w (Function.update S i (f w.1 :: S i))
       done)
    | (simp only [trStmt₁, Turing.TM2.stepAux, prjσ₁, shiSim2_liftStk₁_apply,
         shiSim2_update_liftStk₁]
       apply ih
       done)
  | peek i f q ih =>
    intro w S
    first
    | (exact ih (f w.1 (S i).head?, w.2) S
       done)
    | (have e1 : stepAux (Stmt.peek i f q) w.1 S
             = stepAux q (f w.1 (S i).head?) S := rfl
       have e2 : stepAux (trStmt₁ tm₁ tm₂ (Stmt.peek i f q)) w (liftStk₁ tm₁ tm₂ T S)
             = stepAux (trStmt₁ tm₁ tm₂ q) (f w.1 (S i).head?, w.2)
                 (liftStk₁ tm₁ tm₂ T S) := rfl
       rw [e1, e2]
       exact ih (f w.1 (S i).head?, w.2) S
       done)
    | (simp only [trStmt₁, Turing.TM2.stepAux, prjσ₁, injσ₁, shiSim2_liftStk₁_apply]
       exact ih (f w.1 (S i).head?, w.2) S
       done)
    | (simp only [trStmt₁, Turing.TM2.stepAux, prjσ₁, injσ₁, shiSim2_liftStk₁_apply]
       apply ih
       done)
  | pop i f q ih =>
    intro w S
    first
    | (have e1 : stepAux (Stmt.pop i f q) w.1 S
             = stepAux q (f w.1 (S i).head?) (Function.update S i (S i).tail) := rfl
       have e2 : stepAux (trStmt₁ tm₁ tm₂ (Stmt.pop i f q)) w (liftStk₁ tm₁ tm₂ T S)
             = stepAux (trStmt₁ tm₁ tm₂ q) (f w.1 (S i).head?, w.2)
                 (Function.update (liftStk₁ tm₁ tm₂ T S) (injK₁ tm₁ tm₂ i)
                   (S i).tail) := rfl
       rw [e1, e2, shiSim2_update_liftStk₁]
       exact ih (f w.1 (S i).head?, w.2) (Function.update S i (S i).tail)
       done)
    | (simp only [trStmt₁, Turing.TM2.stepAux, prjσ₁, injσ₁, shiSim2_liftStk₁_apply,
         shiSim2_update_liftStk₁]
       exact ih (f w.1 (S i).head?, w.2) (Function.update S i (S i).tail)
       done)
    | (simp only [trStmt₁, Turing.TM2.stepAux, prjσ₁, injσ₁, shiSim2_liftStk₁_apply,
         shiSim2_update_liftStk₁]
       apply ih
       done)
  | load a q ih =>
    intro w S
    first
    | (exact ih (a w.1, w.2) S
       done)
    | (have e1 : stepAux (Stmt.load a q) w.1 S = stepAux q (a w.1) S := rfl
       have e2 : stepAux (trStmt₁ tm₁ tm₂ (Stmt.load a q)) w (liftStk₁ tm₁ tm₂ T S)
             = stepAux (trStmt₁ tm₁ tm₂ q) (a w.1, w.2) (liftStk₁ tm₁ tm₂ T S) := rfl
       rw [e1, e2]
       exact ih (a w.1, w.2) S
       done)
    | (simp only [trStmt₁, Turing.TM2.stepAux, prjσ₁, injσ₁]
       exact ih (a w.1, w.2) S
       done)
    | (simp only [trStmt₁, Turing.TM2.stepAux, prjσ₁, injσ₁]
       apply ih
       done)
  | branch c q₁ q₂ ih₁ ih₂ =>
    intro w S
    first
    | (have e1 : stepAux (Stmt.branch c q₁ q₂) w.1 S
             = cond (c w.1) (stepAux q₁ w.1 S) (stepAux q₂ w.1 S) := rfl
       have e2 : stepAux (trStmt₁ tm₁ tm₂ (Stmt.branch c q₁ q₂)) w (liftStk₁ tm₁ tm₂ T S)
             = cond (c w.1) (stepAux (trStmt₁ tm₁ tm₂ q₁) w (liftStk₁ tm₁ tm₂ T S))
                 (stepAux (trStmt₁ tm₁ tm₂ q₂) w (liftStk₁ tm₁ tm₂ T S)) := rfl
       rw [e1, e2]
       rcases Bool.eq_false_or_eq_true (c w.1) with hc | hc <;>
         first
         | (simp only [hc, cond_true]
            exact ih₁ w S
            done)
         | (simp only [hc, cond_false]
            exact ih₂ w S
            done)
       done)
    | (simp only [trStmt₁, Turing.TM2.stepAux, prjσ₁]
       rcases Bool.eq_false_or_eq_true (c w.1) with hc | hc <;>
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
    | (simp only [trStmt₁, Turing.TM2.stepAux, prjσ₁, Option.elim_some]
       done)
    | (simp only [trStmt₁, Turing.TM2.stepAux, prjσ₁, Option.elim_some]
       rfl
       done)
    | (simp [trStmt₁, Turing.TM2.stepAux, prjσ₁]
       done)
  | halt =>
    intro w S
    first
    | (rfl
       done)
    | (simp only [trStmt₁, Turing.TM2.stepAux, Option.elim_none]
       done)
    | (simp only [trStmt₁, Turing.TM2.stepAux, Option.elim_none]
       rfl
       done)
    | (simp [trStmt₁, Turing.TM2.stepAux]
       done)

/-- **Step-exact simulation of the first component of the sequential composite.**

Fix `tm₁ tm₂ : Turing.FinTM2` and a family `T` of background stacks of the composite (the
second machine's stacks and the scratch stack).  For every statement `q` of the first
machine, every composite internal state `w : tm₁.σ × tm₂.σ × Option (tm₂.Γ tm₂.k₀)` and
every stack family `S` of the first machine:

1. one `Turing.TM2.stepAux` of the translated statement `ShiTM2.trStmt₁ tm₁ tm₂ q`, run on
   the lifted stacks `ShiTM2.liftStk₁ tm₁ tm₂ T S`, is the `ShiTM2.liftCfg₁`-lift of one
   `stepAux` of `q` run on `S`.  In particular the first machine's stacks change exactly
   as they do in its own run, the background stacks `T` are untouched, and the second
   state component `w.2.1` and the transfer register `w.2.2` are unchanged;
2. the same, with the state and stack components spelled out, so that the statement can be
   used without unfolding `ShiTM2.liftCfg₁`;
3. if running `q` reaches a `goto` leaf, so that its label is `some l`, then running
   `ShiTM2.trStmt₁ tm₁ tm₂ q` reaches `some (ShiTM2.injΛ₁ tm₁ tm₂ l)`: a plain
   relabelling;
4. **and, asymmetrically, if running `q` reaches a `halt` leaf -- so that its label is
   `none`, at which point `Turing.TM2.step` makes the machine dead and unresumable -- then
   running `ShiTM2.trStmt₁ tm₁ tm₂ q` instead lands on
   `some (ShiTM2.lcopyA tm₁ tm₂)`, the entry label of the copy phase, and the composite is
   still live.**

Conjunct 4 is the entire purpose of the translation `ShiTM2.trStmt₁`: it is what allows a
composite machine to continue after its first component has "halted", which
`Turing.TM2.step ⟨none, _, _⟩ = none` otherwise forbids.  Note that conjuncts 3 and 4
speak of the leaf actually *reached*, not of the top constructor of `q`, because
`stepAux` recurses the entire `Stmt` tree inside a single `Turing.TM2.step`; so, e.g.,
`Stmt.push k f Stmt.halt` also dies in one step, and is also redirected.

The two `DecidableEq` binders are needed because the `kDecidableEq` field of
`Turing.FinTM2` is a structure field, not an instance; `tm₁.kDecidableEq` and
`ShiTM2.compKDecEq tm₁ tm₂` are the intended arguments. -/
theorem solution (tm₁ tm₂ : Turing.FinTM2) [DecidableEq tm₁.K]
    [DecidableEq (CompK tm₁ tm₂)] (T : ∀ k, List (CompΓ tm₁ tm₂ k)) :
    (∀ (q : Stmt tm₁.Γ tm₁.Λ tm₁.σ) (w : Compσ tm₁ tm₂) (S : ∀ i, List (tm₁.Γ i)),
        stepAux (trStmt₁ tm₁ tm₂ q) w (liftStk₁ tm₁ tm₂ T S)
          = liftCfg₁ tm₁ tm₂ T w.2.1 w.2.2 (stepAux q w.1 S))
  ∧ (∀ (q : Stmt tm₁.Γ tm₁.Λ tm₁.σ) (w : Compσ tm₁ tm₂) (S : ∀ i, List (tm₁.Γ i)),
        (stepAux (trStmt₁ tm₁ tm₂ q) w (liftStk₁ tm₁ tm₂ T S)).var
            = ((stepAux q w.1 S).var, w.2.1, w.2.2)
      ∧ (stepAux (trStmt₁ tm₁ tm₂ q) w (liftStk₁ tm₁ tm₂ T S)).stk
            = liftStk₁ tm₁ tm₂ T (stepAux q w.1 S).stk)
  ∧ (∀ (q : Stmt tm₁.Γ tm₁.Λ tm₁.σ) (w : Compσ tm₁ tm₂) (S : ∀ i, List (tm₁.Γ i))
        (l : tm₁.Λ), (stepAux q w.1 S).l = Option.some l →
        (stepAux (trStmt₁ tm₁ tm₂ q) w (liftStk₁ tm₁ tm₂ T S)).l
          = Option.some (injΛ₁ tm₁ tm₂ l))
  ∧ (∀ (q : Stmt tm₁.Γ tm₁.Λ tm₁.σ) (w : Compσ tm₁ tm₂) (S : ∀ i, List (tm₁.Γ i)),
        (stepAux q w.1 S).l = Option.none →
        (stepAux (trStmt₁ tm₁ tm₂ q) w (liftStk₁ tm₁ tm₂ T S)).l
          = Option.some (lcopyA tm₁ tm₂)) := by
  have H := shiSim2_stepAux_lift₁ tm₁ tm₂ T
  refine ⟨fun q w S => ?_, fun q w S => ⟨?_, ?_⟩, fun q w S l hl => ?_,
    fun q w S hl => ?_⟩
  · first
    | (exact H q w S
       done)
    | (rw [H q w S]
       done)
    | (rw [H q w S]
       rfl
       done)
    | (simp only [H q w S, liftCfg₁]
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
    | (rw [H q w S, hl]
       done)
    | (rw [H q w S, hl]
       rfl
       done)
    | (simp only [H q w S, hl, Option.elim_some]
       done)
  · first
    | (rw [H q w S, hl]
       done)
    | (rw [H q w S, hl]
       rfl
       done)
    | (simp only [H q w S, hl, Option.elim_none]
       done)
