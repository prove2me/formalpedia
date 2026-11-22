-- Prove2me | solution 1 for ShiTM.iterate_compM_two_simulation
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-14T21:58:59.574163+00:00
-- url     : https://prove2.me/submissions/8d2c7373-7fbd-4c5c-87db-4e5c7259a1f5

import Definitions.Def_ShiTM2_Composite
import Theorems.Thm_ShiTM_stepAux_trStmt_two_simulation

set_option autoImplicit false

open Turing.TM2 ShiTM2

/-!
# From `stepAux` to `step`, and from `step` to a step-exact iteration -- SECOND component

`ShiTM.stepAux_trStmt_two_simulation` (published, proved) is a fact about a single
`Turing.TM2.Stmt`.  This file turns it into a fact about *machine steps* and then about
*runs* of phase 3 of the sequential composite `ShiTM2.compM` of
`Definitions/Def_ShiTM2_Composite.lean`, i.e. the part of the run that happens after the
copy phase has delivered the intermediate string onto `injK₂ tm₂.k₀`.

## (a) One step

`Turing.TM2.step` is defined by
```
def step (M : Λ → Stmt Γ Λ σ) : Cfg Γ Λ σ → Option (Cfg Γ Λ σ)
  | ⟨none, _, _⟩ => none
  | ⟨some l, v, S⟩ => some (stepAux (M l) v S)
```
(`Mathlib/Computability/TuringMachine/StackTuringMachine.lean:172-175`).  Mathlib provides
**no** hand-written equation lemma for the second branch; there are only the auto-generated
`step.eq_1`/`step.eq_2`, declared `@[simp]` at ibid. `:177-178`, and nowhere in Mathlib is
either cited by name.  Following `Turing.TM2.step_run` (ibid. `:490-494`), which proves a
statement of exactly this shape -- `Function.update` included -- by a bare `rfl`, the
dispatch here is definitional: `step (compM tm₁ tm₂ tr dflt) ⟨some (injΛ₂ tm₁ tm₂ l), w, U⟩`
reduces by `rfl` to `some (stepAux (trStmt₂ tm₁ tm₂ (tm₂.m l)) w U)`, because `injΛ₂` is
`Sum.inr ∘ Sum.inl` and `compM` matches on it.

## How this differs from the first component -- it is not a rename

1. **`trStmt₂` maps `Stmt.halt` to `Stmt.halt`.**  Only the *first* machine has to be
   resumed (its `halt` leaves are redirected to `lcopyA`, which is the whole reason
   `trStmt₁ ≠ trStmt₂`).  The second machine's halt **is** the composite's halt, so
   `liftCfg₂`'s label field is a plain `Option.map (injΛ₂ tm₁ tm₂)` and the accepted
   simulation lemma states **one uniform label law** instead of the first component's
   `some`/`none` split.
2. **There is consequently no liveness conjunct here, and stating one would be false.**
   Where the first-component file concluded `c.l ≠ none` -- the composite is never dead
   after a first-component step -- the correct statement for the second component is that
   **halting is faithfully propagated**: the composite's label after the step is `none`
   *exactly when* the component's own `stepAux` label is `none` (conjunct 6, an `Iff`),
   together with the explicit halted configuration (conjunct 5).  Dying here is the desired
   terminal behaviour of the whole composite, not a failure to be ruled out; a `≠ none`
   claim would contradict conjunct 5.
3. **The component's state is `w.2.1` (`ShiTM2.prjσ₂`), not `w.1`**, its stacks live in the
   `injK₂` block via `liftStk₂`, and the relevant decidable-equality binder is
   `[DecidableEq tm₂.K]`.  The untouched state components are the first machine's final
   state `w₁` and the transfer register `r`, which sit in positions 1 and 3.

## (b) A step-exact iteration

`solution_iterate` is phrased in the idiom of the accepted
`ShiTM.copy_loop_transfers_stack`: an equation between `n`-fold iterates of
`fun c => c.bind (Turing.TM2.step M)` on `Option`-valued configurations, plus a
`Nonempty (StateTransition.EvalsToInTime ...)` conjunct (the iterate equation *is* the
`evals_in_steps` field, `Mathlib/Computability/StateTransition.lean:255-268`; the structure
lives in `Type`, so a theorem cannot return one bare).

The no-intermediate-halt hypothesis is kept in the **same form the accepted
first-component file uses**: "for all `j < n`, the `j`-th configuration of the component run
is `some ⟨some l', v', S'⟩`".  It is not removable -- a component that halts at step
`j < n` has `none` from step `j+1` on, and `Option.bind` propagates that, so nothing
identifies the two runs past that point.  At `j = n` the component **may** halt: that case
is fine and is covered by the uniform `Option.map` label law, which is precisely what makes
the second component's iteration cleaner than the first's.

The induction peels the **last** step (`Function.iterate_succ_apply'`), not the first: the
start configuration then never changes, so `l`, `v`, `S` need not be generalised and the
induction step consumes liveness only at `j = n`.  Peeling the front would force an `n = 0`
case split, since the second configuration may already be the halted one.

## Lemmas cited, all at revision 0df444a360eaa60ab8c11dca51a86af692955474

* `ShiTM.stepAux_trStmt_two_simulation` -- published, proved; imported stub
  `Theorems/Thm_ShiTM_stepAux_trStmt_two_simulation.lean`
* `Turing.TM2.step`, `Turing.TM2.stepAux`, `Turing.TM2.Cfg` --
  `Mathlib/Computability/TuringMachine/StackTuringMachine.lean:172`, `:161`, `:144`
* `Turing.TM2.step_run` -- ibid. `:490` (the precedent for proving `step`/`stepAux`
  equations by `rfl`)
* `StateTransition.EvalsToInTime` -- `Mathlib/Computability/StateTransition.lean:265`
* `Function.iterate_succ_apply'`, `Function.iterate_zero_apply` --
  `Mathlib/Logic/Function/Iterate.lean`
* `Option.map_some`, `Option.map_none`, `Option.bind_some` -- core
  `Init/Data/Option/Basic.lean` / `Init/Data/Option/Lemmas.lean`
-/

/-- The lift of a *live* second-component configuration, written out.  True by `rfl`:
`liftCfg₂` is a structure instance and `Option.map (injΛ₂ ..) (some l)` is
`some (injΛ₂ .. l)`. -/
private theorem shiStepB_liftCfg2_some (tm₁ tm₂ : Turing.FinTM2)
    (T : ∀ k, List (CompΓ tm₁ tm₂ k)) (w₁ : tm₁.σ) (r : Option (tm₂.Γ tm₂.k₀))
    (l : tm₂.Λ) (v : tm₂.σ) (S : ∀ i, List (tm₂.Γ i)) :
    liftCfg₂ tm₁ tm₂ T w₁ r ⟨Option.some l, v, S⟩
      = (⟨Option.some (injΛ₂ tm₁ tm₂ l), ((w₁, v, r) : Compσ tm₁ tm₂),
          liftStk₂ tm₁ tm₂ T S⟩ : CompCfg tm₁ tm₂) := by
  first
  | (rfl
     done)
  | (simp only [liftCfg₂, Option.map_some]
     done)
  | (unfold liftCfg₂
     simp only [Option.map_some]
     done)

/-- **Halting is faithfully propagated by `liftCfg₂`.**  This is the second component's
replacement for the first component's liveness statement: the lifted configuration is halted
exactly when the component configuration is, because `liftCfg₂`'s label field is a plain
`Option.map` (contrast `liftCfg₁`, which sends `none` to `some (lcopyA ..)`). -/
private theorem shiStepB_halt_iff (tm₁ tm₂ : Turing.FinTM2)
    (T : ∀ k, List (CompΓ tm₁ tm₂ k)) (w₁ : tm₁.σ) (r : Option (tm₂.Γ tm₂.k₀))
    (c : Cfg tm₂.Γ tm₂.Λ tm₂.σ) :
    (liftCfg₂ tm₁ tm₂ T w₁ r c).l = Option.none ↔ c.l = Option.none := by
  have hl : (liftCfg₂ tm₁ tm₂ T w₁ r c).l = (c.l).map (injΛ₂ tm₁ tm₂) := rfl
  rw [hl]
  cases hc : c.l with
  | none =>
    first
    | (simp only [hc, Option.map_none]
       done)
    | (simp [hc]
       done)
    | (exact Iff.rfl
       done)
  | some l' =>
    first
    | (simp only [hc, Option.map_some]
       done)
    | (simp [hc]
       done)

/-- **The dispatch step.**  One `Turing.TM2.step` of the composite at a *second*-component
label runs the translated second-component statement.  Definitional: `step`'s second branch
applies because the label is `Option.some _`, and `compM`'s second branch applies because
`injΛ₂` is `Sum.inr (Sum.inl _)`.  Exactly the shape Mathlib itself proves by `rfl` in
`Turing.TM2.step_run` (`StackTuringMachine.lean:490-494`). -/
private theorem shiStepB_dispatch (tm₁ tm₂ : Turing.FinTM2) [DecidableEq tm₂.K]
    [DecidableEq (CompK tm₁ tm₂)] (tr : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (dflt : tm₂.Γ tm₂.k₀) (T : ∀ k, List (CompΓ tm₁ tm₂ k)) (w₁ : tm₁.σ)
    (r : Option (tm₂.Γ tm₂.k₀)) (l : tm₂.Λ) (v : tm₂.σ) (S : ∀ i, List (tm₂.Γ i)) :
    step (compM tm₁ tm₂ tr dflt)
        (⟨Option.some (injΛ₂ tm₁ tm₂ l), ((w₁, v, r) : Compσ tm₁ tm₂),
          liftStk₂ tm₁ tm₂ T S⟩ : CompCfg tm₁ tm₂)
      = Option.some (stepAux (trStmt₂ tm₁ tm₂ (tm₂.m l)) ((w₁, v, r) : Compσ tm₁ tm₂)
          (liftStk₂ tm₁ tm₂ T S)) := by
  first
  | (rfl
     done)
  | (simp only [step, compM, injΛ₂]
     done)
  | (simp only [Turing.TM2.step.eq_2, compM, injΛ₂]
     done)

/-- **One composite step is the lift of one second-component step**, in explicit form. -/
private theorem shiStepB_step_explicit (tm₁ tm₂ : Turing.FinTM2) [DecidableEq tm₂.K]
    [DecidableEq (CompK tm₁ tm₂)] (tr : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (dflt : tm₂.Γ tm₂.k₀) (T : ∀ k, List (CompΓ tm₁ tm₂ k)) (w₁ : tm₁.σ)
    (r : Option (tm₂.Γ tm₂.k₀)) (l : tm₂.Λ) (v : tm₂.σ) (S : ∀ i, List (tm₂.Γ i)) :
    step (compM tm₁ tm₂ tr dflt)
        (⟨Option.some (injΛ₂ tm₁ tm₂ l), ((w₁, v, r) : Compσ tm₁ tm₂),
          liftStk₂ tm₁ tm₂ T S⟩ : CompCfg tm₁ tm₂)
      = Option.some (liftCfg₂ tm₁ tm₂ T w₁ r (stepAux (tm₂.m l) v S)) := by
  have H := ShiTM.stepAux_trStmt_two_simulation tm₁ tm₂ T
  have hsim := H.1 (tm₂.m l) ((w₁, v, r) : Compσ tm₁ tm₂) S
  first
  | (rw [shiStepB_dispatch tm₁ tm₂ tr dflt T w₁ r l v S, hsim]
     done)
  | (rw [shiStepB_dispatch tm₁ tm₂ tr dflt T w₁ r l v S, hsim]
     rfl
     done)
  | (rw [shiStepB_dispatch tm₁ tm₂ tr dflt T w₁ r l v S]
     exact congrArg Option.some hsim
     done)
  | (exact congrArg Option.some hsim
     done)

/-- One composite step, in the `liftCfg₂`/`Option.map` form used by the iteration below. -/
private theorem shiStepB_step_lift (tm₁ tm₂ : Turing.FinTM2) [DecidableEq tm₂.K]
    [DecidableEq (CompK tm₁ tm₂)] (tr : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (dflt : tm₂.Γ tm₂.k₀) (T : ∀ k, List (CompΓ tm₁ tm₂ k)) (w₁ : tm₁.σ)
    (r : Option (tm₂.Γ tm₂.k₀)) (l : tm₂.Λ) (v : tm₂.σ) (S : ∀ i, List (tm₂.Γ i)) :
    step (compM tm₁ tm₂ tr dflt) (liftCfg₂ tm₁ tm₂ T w₁ r ⟨Option.some l, v, S⟩)
      = (step tm₂.m (⟨Option.some l, v, S⟩ : Cfg tm₂.Γ tm₂.Λ tm₂.σ)).map
          (liftCfg₂ tm₁ tm₂ T w₁ r) := by
  have hexp := shiStepB_step_explicit tm₁ tm₂ tr dflt T w₁ r l v S
  first
  | (rw [shiStepB_liftCfg2_some tm₁ tm₂ T w₁ r l v S, hexp]
     done)
  | (rw [shiStepB_liftCfg2_some tm₁ tm₂ T w₁ r l v S, hexp]
     rfl
     done)
  | (exact hexp
     done)
  | (rw [shiStepB_liftCfg2_some tm₁ tm₂ T w₁ r l v S, hexp]
     simp only [step, Option.map_some]
     done)

/-- **(a) One step of the composite machine at a second-component label.**

Fix `tm₁ tm₂ : Turing.FinTM2`, a symbol translation `tr` and dummy symbol `dflt` (the data
of `ShiTM2.comp`), a family `T` of background stacks (the first machine's stacks and the
scratch stack, which phase 3 never touches), the first machine's final state `w₁` and the
transfer register `r`.  Then for every second-component label `l`, state `v` and stack
family `S`:

1. **dispatch**: one `Turing.TM2.step` of `ShiTM2.compM tm₁ tm₂ tr dflt` from the lifted
   configuration `⟨some (injΛ₂ tm₁ tm₂ l), (w₁, v, r), liftStk₂ tm₁ tm₂ T S⟩` is
   `some (stepAux (trStmt₂ tm₁ tm₂ (tm₂.m l)) (w₁, v, r) (liftStk₂ tm₁ tm₂ T S))` -- the
   composite really does run the translated program of the second component there;
2. and that is `some` of the `ShiTM2.liftCfg₂`-lift of the second component's own
   `stepAux (tm₂.m l) v S`: the component's stacks move as they do in its own run, the
   background stacks `T` are untouched, and `w₁`, `r` are unchanged;
3. equivalently, in `Option.map` form and with the source configuration itself written as a
   `liftCfg₂`, one composite step is the lift of one component `Turing.TM2.step` -- the form
   that iterates;
4. **goto leaf**: if the component's step lands on a label `some l'`, the composite lands on
   `some (injΛ₂ tm₁ tm₂ l')`, with the state and stacks lifted -- a plain relabelling;
5. **halt leaf**: if the component's step lands on `none`, the composite lands on `none`
   **too** -- `trStmt₂` leaves `Stmt.halt` alone, so the second component's halt *is* the
   composite's halt.  This is where the second component differs from the first, whose
   `halt` leaves are redirected to `ShiTM2.lcopyA` by `trStmt₁` because a halted TM2 is dead
   (`Turing.TM2.step M ⟨none, _, _⟩ = none`, `StackTuringMachine.lean:172-173`) and the
   first machine still has to be sequenced after;
6. consequently halting is **faithfully propagated**, in both directions: the step always
   produces a configuration `c`, whose label is the `Option.map (injΛ₂ tm₁ tm₂)` of the
   component's, and `c.l = none` **if and only if** the component's own `stepAux` label is
   `none`.  There is deliberately no `c.l ≠ none` liveness claim here -- it would be false,
   by conjunct 5, and it is not wanted: the composite is *supposed* to die exactly when
   `tm₂` does.

Note that conjuncts 4 and 5 speak of the leaf actually *reached*, not of the top constructor
of `tm₂.m l`: `stepAux` recurses the entire `Stmt` tree inside one `Turing.TM2.step`.

The two `DecidableEq` binders are structure fields of `Turing.FinTM2`, not instances;
`tm₂.kDecidableEq` and `ShiTM2.compKDecEq tm₁ tm₂` are the intended arguments. -/
private theorem shiStepB_pack (tm₁ tm₂ : Turing.FinTM2) [DecidableEq tm₂.K]
    [DecidableEq (CompK tm₁ tm₂)] (tr : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (dflt : tm₂.Γ tm₂.k₀) (T : ∀ k, List (CompΓ tm₁ tm₂ k)) (w₁ : tm₁.σ)
    (r : Option (tm₂.Γ tm₂.k₀)) :
    (∀ (l : tm₂.Λ) (v : tm₂.σ) (S : ∀ i, List (tm₂.Γ i)),
        step (compM tm₁ tm₂ tr dflt)
            (⟨Option.some (injΛ₂ tm₁ tm₂ l), ((w₁, v, r) : Compσ tm₁ tm₂),
              liftStk₂ tm₁ tm₂ T S⟩ : CompCfg tm₁ tm₂)
          = Option.some (stepAux (trStmt₂ tm₁ tm₂ (tm₂.m l)) ((w₁, v, r) : Compσ tm₁ tm₂)
              (liftStk₂ tm₁ tm₂ T S)))
  ∧ (∀ (l : tm₂.Λ) (v : tm₂.σ) (S : ∀ i, List (tm₂.Γ i)),
        step (compM tm₁ tm₂ tr dflt)
            (⟨Option.some (injΛ₂ tm₁ tm₂ l), ((w₁, v, r) : Compσ tm₁ tm₂),
              liftStk₂ tm₁ tm₂ T S⟩ : CompCfg tm₁ tm₂)
          = Option.some (liftCfg₂ tm₁ tm₂ T w₁ r (stepAux (tm₂.m l) v S)))
  ∧ (∀ (l : tm₂.Λ) (v : tm₂.σ) (S : ∀ i, List (tm₂.Γ i)),
        step (compM tm₁ tm₂ tr dflt) (liftCfg₂ tm₁ tm₂ T w₁ r ⟨Option.some l, v, S⟩)
          = (step tm₂.m (⟨Option.some l, v, S⟩ : Cfg tm₂.Γ tm₂.Λ tm₂.σ)).map
              (liftCfg₂ tm₁ tm₂ T w₁ r))
  ∧ (∀ (l : tm₂.Λ) (v : tm₂.σ) (S : ∀ i, List (tm₂.Γ i)) (l' : tm₂.Λ),
        (stepAux (tm₂.m l) v S).l = Option.some l' →
        step (compM tm₁ tm₂ tr dflt)
            (⟨Option.some (injΛ₂ tm₁ tm₂ l), ((w₁, v, r) : Compσ tm₁ tm₂),
              liftStk₂ tm₁ tm₂ T S⟩ : CompCfg tm₁ tm₂)
          = Option.some (⟨Option.some (injΛ₂ tm₁ tm₂ l'),
              ((w₁, (stepAux (tm₂.m l) v S).var, r) : Compσ tm₁ tm₂),
              liftStk₂ tm₁ tm₂ T (stepAux (tm₂.m l) v S).stk⟩ : CompCfg tm₁ tm₂))
  ∧ (∀ (l : tm₂.Λ) (v : tm₂.σ) (S : ∀ i, List (tm₂.Γ i)),
        (stepAux (tm₂.m l) v S).l = Option.none →
        step (compM tm₁ tm₂ tr dflt)
            (⟨Option.some (injΛ₂ tm₁ tm₂ l), ((w₁, v, r) : Compσ tm₁ tm₂),
              liftStk₂ tm₁ tm₂ T S⟩ : CompCfg tm₁ tm₂)
          = Option.some (⟨Option.none,
              ((w₁, (stepAux (tm₂.m l) v S).var, r) : Compσ tm₁ tm₂),
              liftStk₂ tm₁ tm₂ T (stepAux (tm₂.m l) v S).stk⟩ : CompCfg tm₁ tm₂))
  ∧ (∀ (l : tm₂.Λ) (v : tm₂.σ) (S : ∀ i, List (tm₂.Γ i)),
        ∃ c : CompCfg tm₁ tm₂,
          step (compM tm₁ tm₂ tr dflt)
              (⟨Option.some (injΛ₂ tm₁ tm₂ l), ((w₁, v, r) : Compσ tm₁ tm₂),
                liftStk₂ tm₁ tm₂ T S⟩ : CompCfg tm₁ tm₂) = Option.some c
        ∧ c.l = ((stepAux (tm₂.m l) v S).l).map (injΛ₂ tm₁ tm₂)
        ∧ (c.l = Option.none ↔ (stepAux (tm₂.m l) v S).l = Option.none)) := by
  refine ⟨fun l v S => shiStepB_dispatch tm₁ tm₂ tr dflt T w₁ r l v S,
    fun l v S => shiStepB_step_explicit tm₁ tm₂ tr dflt T w₁ r l v S,
    fun l v S => shiStepB_step_lift tm₁ tm₂ tr dflt T w₁ r l v S,
    fun l v S l' hl => ?_, fun l v S hl => ?_, fun l v S => ?_⟩
  · first
    | (rw [shiStepB_step_explicit tm₁ tm₂ tr dflt T w₁ r l v S, liftCfg₂, hl]
       done)
    | (rw [shiStepB_step_explicit tm₁ tm₂ tr dflt T w₁ r l v S]
       simp only [liftCfg₂, hl, Option.map_some]
       done)
    | (rw [shiStepB_step_explicit tm₁ tm₂ tr dflt T w₁ r l v S]
       unfold liftCfg₂
       rw [hl]
       done)
    | (rw [shiStepB_step_explicit tm₁ tm₂ tr dflt T w₁ r l v S]
       unfold liftCfg₂
       simp only [hl, Option.map_some]
       done)
    | (rw [shiStepB_step_explicit tm₁ tm₂ tr dflt T w₁ r l v S]
       congr 1
       unfold liftCfg₂
       simp only [hl, Option.map_some]
       done)
    | (rw [shiStepB_step_explicit tm₁ tm₂ tr dflt T w₁ r l v S]
       simp [liftCfg₂, hl]
       done)
    | (rw [shiStepB_step_explicit tm₁ tm₂ tr dflt T w₁ r l v S]
       congr 1
       simp [liftCfg₂, hl]
       done)
  · first
    | (rw [shiStepB_step_explicit tm₁ tm₂ tr dflt T w₁ r l v S, liftCfg₂, hl]
       done)
    | (rw [shiStepB_step_explicit tm₁ tm₂ tr dflt T w₁ r l v S]
       simp only [liftCfg₂, hl, Option.map_none]
       done)
    | (rw [shiStepB_step_explicit tm₁ tm₂ tr dflt T w₁ r l v S]
       unfold liftCfg₂
       rw [hl]
       done)
    | (rw [shiStepB_step_explicit tm₁ tm₂ tr dflt T w₁ r l v S]
       unfold liftCfg₂
       simp only [hl, Option.map_none]
       done)
    | (rw [shiStepB_step_explicit tm₁ tm₂ tr dflt T w₁ r l v S]
       congr 1
       unfold liftCfg₂
       simp only [hl, Option.map_none]
       done)
    | (rw [shiStepB_step_explicit tm₁ tm₂ tr dflt T w₁ r l v S]
       simp [liftCfg₂, hl]
       done)
    | (rw [shiStepB_step_explicit tm₁ tm₂ tr dflt T w₁ r l v S]
       congr 1
       simp [liftCfg₂, hl]
       done)
  · refine ⟨liftCfg₂ tm₁ tm₂ T w₁ r (stepAux (tm₂.m l) v S),
      shiStepB_step_explicit tm₁ tm₂ tr dflt T w₁ r l v S, ?_,
      shiStepB_halt_iff tm₁ tm₂ T w₁ r (stepAux (tm₂.m l) v S)⟩
    first
    | (rfl
       done)
    | (simp only [liftCfg₂]
       done)
    | (unfold liftCfg₂
       rfl
       done)

/-! ### (b) The step-exact iteration -/

/-- The iteration, by induction on `n`, peeling the **last** step.  `l`, `v`, `S` are fixed
throughout: peeling from the back leaves the start configuration alone, so only liveness at
`j = n` is consumed in the induction step. -/
private theorem shiStepB_iterate (tm₁ tm₂ : Turing.FinTM2) [DecidableEq tm₂.K]
    [DecidableEq (CompK tm₁ tm₂)] (tr : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (dflt : tm₂.Γ tm₂.k₀) (T : ∀ k, List (CompΓ tm₁ tm₂ k)) (w₁ : tm₁.σ)
    (r : Option (tm₂.Γ tm₂.k₀)) (l : tm₂.Λ) (v : tm₂.σ) (S : ∀ i, List (tm₂.Γ i)) :
    ∀ n : ℕ,
      (∀ j < n, ∃ (l' : tm₂.Λ) (v' : tm₂.σ) (S' : ∀ i, List (tm₂.Γ i)),
          (fun c : Option (Cfg tm₂.Γ tm₂.Λ tm₂.σ) => c.bind (step tm₂.m))^[j]
              (Option.some (⟨Option.some l, v, S⟩ : Cfg tm₂.Γ tm₂.Λ tm₂.σ))
            = Option.some (⟨Option.some l', v', S'⟩ : Cfg tm₂.Γ tm₂.Λ tm₂.σ)) →
      (fun c : Option (CompCfg tm₁ tm₂) => c.bind (step (compM tm₁ tm₂ tr dflt)))^[n]
          (Option.some (liftCfg₂ tm₁ tm₂ T w₁ r ⟨Option.some l, v, S⟩))
        = ((fun c : Option (Cfg tm₂.Γ tm₂.Λ tm₂.σ) => c.bind (step tm₂.m))^[n]
            (Option.some (⟨Option.some l, v, S⟩ : Cfg tm₂.Γ tm₂.Λ tm₂.σ))).map
              (liftCfg₂ tm₁ tm₂ T w₁ r) := by
  intro n
  induction n with
  | zero =>
    intro _
    first
    | (simp only [Function.iterate_zero_apply, Option.map_some]
       done)
    | (rfl
       done)
  | succ n ih =>
    intro hlive
    have ihn := ih (fun j hj => hlive j (by omega))
    obtain ⟨l', v', S', hn⟩ := hlive n (by omega)
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ihn, hn]
    first
    | (exact shiStepB_step_lift tm₁ tm₂ tr dflt T w₁ r l' v' S'
       done)
    | (simp only [Option.map_some, Option.bind_some]
       exact shiStepB_step_lift tm₁ tm₂ tr dflt T w₁ r l' v' S'
       done)
    | (simp only [Option.map_some, Option.bind_some,
         shiStepB_step_lift tm₁ tm₂ tr dflt T w₁ r l' v' S']
       done)

/-- **(b) Step-exact iteration of the second component inside the composite.**

Suppose the second component, started at `⟨some l, v, S⟩` (in the assembly: at
`⟨some tm₂.main, tm₂.initialState, Turing.initList tm₂ _⟩`, the configuration the copy phase
delivers), stays **live for the first `n` configurations**: for every `j < n` its `j`-th
configuration exists and has a `some` label, i.e. is of the form `⟨some l', v', S'⟩`.  Then:

1. the composite's `n`-fold iterate from the lifted start configuration
   `ShiTM2.liftCfg₂ tm₁ tm₂ T w₁ r ⟨some l, v, S⟩` is the `Option.map`-lift of the
   component's own `n`-fold iterate -- an equation between iterates of
   `fun c => c.bind (Turing.TM2.step _)`, which is the `evals_in_steps` field of
   `StateTransition.EvalsTo`;
2. hence if the component reaches a configuration `c` in **exactly** `n` steps, the
   composite reaches `ShiTM2.liftCfg₂ tm₁ tm₂ T w₁ r c` in exactly `n` steps, packaged as
   `StateTransition.EvalsToInTime ... n`, ready to be chained after the copy phase (supplied
   by `ShiTM.copy_loop_transfers_stack`) with `StateTransition.EvalsToInTime.trans`, whose
   index is `m₂ + m₁`, reversed.

Unlike for the first component, `c` here is allowed to be the **halted** configuration
`⟨none, _, _⟩`: the liveness hypothesis is only imposed for `j < n`, and at `j = n` the
uniform `Option.map` label law of `ShiTM2.liftCfg₂` carries `none` to `none`, so the
composite halts exactly there.  That is the intended terminal behaviour of the whole
composite, which is why no `≠ none` conclusion appears anywhere in this file.

The liveness hypothesis for `j < n` is necessary, not cosmetic: a component that halts at
step `j < n` has `none` as its `(j+1)`-st configuration and `Option.bind` keeps it `none`
thereafter, so nothing identifies the two runs past that point.  Its `j = 0` instance is
trivially satisfiable (`l' := l`, `v' := v`, `S' := S`), and liveness at `j` already implies
that the `(j+1)`-st configuration exists, so the hypothesis constrains labels only. -/
theorem solution (tm₁ tm₂ : Turing.FinTM2) [DecidableEq tm₂.K]
    [DecidableEq (CompK tm₁ tm₂)] (tr : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (dflt : tm₂.Γ tm₂.k₀) (T : ∀ k, List (CompΓ tm₁ tm₂ k)) (w₁ : tm₁.σ)
    (r : Option (tm₂.Γ tm₂.k₀)) (n : ℕ) (l : tm₂.Λ) (v : tm₂.σ)
    (S : ∀ i, List (tm₂.Γ i))
    (hlive : ∀ j < n, ∃ (l' : tm₂.Λ) (v' : tm₂.σ) (S' : ∀ i, List (tm₂.Γ i)),
        (fun c : Option (Cfg tm₂.Γ tm₂.Λ tm₂.σ) => c.bind (step tm₂.m))^[j]
            (Option.some (⟨Option.some l, v, S⟩ : Cfg tm₂.Γ tm₂.Λ tm₂.σ))
          = Option.some (⟨Option.some l', v', S'⟩ : Cfg tm₂.Γ tm₂.Λ tm₂.σ)) :
    (fun c : Option (CompCfg tm₁ tm₂) => c.bind (step (compM tm₁ tm₂ tr dflt)))^[n]
        (Option.some (liftCfg₂ tm₁ tm₂ T w₁ r ⟨Option.some l, v, S⟩))
      = ((fun c : Option (Cfg tm₂.Γ tm₂.Λ tm₂.σ) => c.bind (step tm₂.m))^[n]
          (Option.some (⟨Option.some l, v, S⟩ : Cfg tm₂.Γ tm₂.Λ tm₂.σ))).map
            (liftCfg₂ tm₁ tm₂ T w₁ r)
  ∧ (∀ c : Cfg tm₂.Γ tm₂.Λ tm₂.σ,
        (fun c : Option (Cfg tm₂.Γ tm₂.Λ tm₂.σ) => c.bind (step tm₂.m))^[n]
            (Option.some (⟨Option.some l, v, S⟩ : Cfg tm₂.Γ tm₂.Λ tm₂.σ))
          = Option.some c →
        Nonempty (StateTransition.EvalsToInTime (step (compM tm₁ tm₂ tr dflt))
          (liftCfg₂ tm₁ tm₂ T w₁ r ⟨Option.some l, v, S⟩)
          (Option.some (liftCfg₂ tm₁ tm₂ T w₁ r c)) n)) := by
  have hkey := shiStepB_iterate tm₁ tm₂ tr dflt T w₁ r l v S n hlive
  refine ⟨hkey, fun c hc => ?_⟩
  rw [hc] at hkey
  have hkey' : (fun c : Option (CompCfg tm₁ tm₂) =>
      c.bind (step (compM tm₁ tm₂ tr dflt)))^[n]
        (Option.some (liftCfg₂ tm₁ tm₂ T w₁ r ⟨Option.some l, v, S⟩))
      = Option.some (liftCfg₂ tm₁ tm₂ T w₁ r c) := by
    first
    | (exact hkey
       done)
    | (rw [hkey]
       done)
    | (simpa only [Option.map_some] using hkey
       done)
  first
  | (exact ⟨{ steps := n, evals_in_steps := hkey', steps_le_m := le_rfl }⟩
     done)
  | (exact ⟨⟨⟨n, hkey'⟩, le_rfl⟩⟩
     done)
  | (refine ⟨{ steps := n, evals_in_steps := ?_, steps_le_m := le_rfl }⟩
     exact hkey'
     done)
  | (refine ⟨{ steps := n, evals_in_steps := ?_, steps_le_m := le_rfl }⟩
     simpa only [flip] using hkey'
     done)
