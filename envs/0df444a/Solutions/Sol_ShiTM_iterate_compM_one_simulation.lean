-- Prove2me | solution 1 for ShiTM.iterate_compM_one_simulation
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-14T21:09:03.723238+00:00
-- url     : https://prove2.me/submissions/c765cfce-ba25-4a63-b5b3-ba81381512da

import Definitions.Def_ShiTM2_Composite
import Theorems.Thm_ShiTM_stepAux_trStmt_one_simulation

set_option autoImplicit false

open Turing.TM2 ShiTM2

/-!
# From `stepAux` to `step`, and from `step` to a step-exact iteration

`ShiTM.stepAux_trStmt_one_simulation` (published, proved) is a fact about a single
`Turing.TM2.Stmt`.  This file turns it into a fact about *machine steps* and then about
*runs* of the sequential composite `ShiTM2.compM` of
`Definitions/Def_ShiTM2_Composite.lean`.

## (a) One step

`Turing.TM2.step` is defined by
```
def step (M : Λ → Stmt Γ Λ σ) : Cfg Γ Λ σ → Option (Cfg Γ Λ σ)
  | ⟨none, _, _⟩ => none
  | ⟨some l, v, S⟩ => some (stepAux (M l) v S)
```
(`Mathlib/Computability/TuringMachine/StackTuringMachine.lean:172-175`).  Mathlib provides
**no** hand-written equation lemma for the second branch; there are only the
auto-generated `step.eq_1`/`step.eq_2`, declared `@[simp]` at ibid. `:177-178`, and nowhere
in Mathlib is either cited by name.  Following `Turing.TM2.step_run` (ibid. `:490-494`),
which proves a statement of exactly this shape by a bare `rfl`, the dispatch here is
definitional: `step (compM tm₁ tm₂ tr dflt) ⟨some (injΛ₁ tm₁ tm₂ l), w, U⟩` reduces by
`rfl` to `some (stepAux (trStmt₁ tm₁ tm₂ (tm₁.m l)) w U)`, because `injΛ₁` is `Sum.inl`
and `compM` matches on it.  Conjunct 1 of `solution` records that; conjuncts 2 and 3 then
apply the accepted simulation lemma to identify the result with the `liftCfg₁`-lift of the
component's own step.

**Both leaves are covered.**  `liftCfg₁` sends the component label `none` to
`some (lcopyA tm₁ tm₂)` and `some l'` to `some (injΛ₁ tm₁ tm₂ l')`, so the single equation
of conjunct 2 already contains the halt case; conjuncts 4 and 5 spell the two cases out as
explicit configurations, and conjunct 6 records the consequence that matters for
sequencing: **the composite is never dead after such a step**, whereas the component
itself dies (`step M ⟨none, _, _⟩ = none`, ibid. `:172-173`) precisely in case 5.  That is
the entire purpose of the `Stmt.halt ↦ Stmt.goto (fun _ => lcopyA)` clause of `trStmt₁`.

## (b) A step-exact iteration

`solution_iterate` is phrased in the idiom of the accepted
`ShiTM.copy_loop_transfers_stack`: an equation between `n`-fold iterates of
`fun c => c.bind (Turing.TM2.step M)` on `Option`-valued configurations, plus a
`Nonempty (StateTransition.EvalsToInTime ...)` conjunct (the iterate equation *is* the
`evals_in_steps` field, `Mathlib/Computability/StateTransition.lean:255-268`).

The no-intermediate-halt hypothesis is phrased, as anticipated, as **"for all `j < n`, the
`j`-th configuration of the component run exists and has label `some _`"**, written with
an explicit configuration triple `⟨some l', v', S'⟩` so that no separate "is `some`" and
"is live" hypotheses are needed.  It cannot be dropped: if the component halts at step
`j < n` its run is `none` from step `j+1` on, while the composite's run continues from
`lcopyA` into the copy phase, so the two runs genuinely diverge there.  The `j = 0`
instance is trivially satisfiable, and liveness at `j` in fact *implies* that the
`(j+1)`-st configuration exists, so the hypothesis is only about labels.

The induction peels the **last** step (`Function.iterate_succ_apply'`), not the first: the
start configuration then never changes, so `l`, `v`, `S` need not be generalised, and the
induction step needs liveness only at `j = n`.  Peeling the first step instead would force
a case split on `n = 0` (the second configuration may be the halted one).

## Lemmas cited, all at revision 0df444a360eaa60ab8c11dca51a86af692955474

* `ShiTM.stepAux_trStmt_one_simulation` -- published, proved; imported stub
  `Theorems/Thm_ShiTM_stepAux_trStmt_one_simulation.lean`
* `Turing.TM2.step`, `Turing.TM2.stepAux`, `Turing.TM2.Cfg` --
  `Mathlib/Computability/TuringMachine/StackTuringMachine.lean:172`, `:161`, `:144`
* `Turing.TM2.step_run` -- ibid. `:490` (the precedent for proving `step`/`stepAux`
  equations by `rfl`)
* `StateTransition.EvalsToInTime` -- `Mathlib/Computability/StateTransition.lean:265`
* `Function.iterate_succ_apply'` -- `Mathlib/Logic/Function/Iterate.lean`
* `Option.map_some`, `Option.bind_some` -- core `Init/Data/Option/Basic.lean:58,126`
* `Option.elim_some`, `Option.elim_none` -- core `Init/Data/Option/Lemmas.lean:735,737`
* `Option.some_ne_none` -- core `Init/Data/Option/Basic.lean`
-/

/-- The lift of a *live* component configuration, written out.  True by `rfl`:
`liftCfg₁` is a structure instance and `(some l).elim (lcopyA ..) (injΛ₁ ..)` is
`injΛ₁ .. l`. -/
private theorem shiStep_liftCfg1_some (tm₁ tm₂ : Turing.FinTM2)
    (T : ∀ k, List (CompΓ tm₁ tm₂ k)) (w₂ : tm₂.σ) (r : Option (tm₂.Γ tm₂.k₀))
    (l : tm₁.Λ) (v : tm₁.σ) (S : ∀ i, List (tm₁.Γ i)) :
    liftCfg₁ tm₁ tm₂ T w₂ r ⟨Option.some l, v, S⟩
      = (⟨Option.some (injΛ₁ tm₁ tm₂ l), ((v, w₂, r) : Compσ tm₁ tm₂),
          liftStk₁ tm₁ tm₂ T S⟩ : CompCfg tm₁ tm₂) := by
  first
  | (rfl
     done)
  | (simp only [liftCfg₁, Option.elim_some]
     done)
  | (unfold liftCfg₁
     simp only [Option.elim_some]
     done)

/-- **The dispatch step.**  One `Turing.TM2.step` of the composite at a first-component
label runs the translated first-component statement.  Definitional: `step`'s second branch
applies because the label is `Option.some _`, and `compM`'s first branch applies because
`injΛ₁` is `Sum.inl`.  This is the `step`-level content of part (a), and it is exactly the
shape Mathlib itself proves by `rfl` in `Turing.TM2.step_run`
(`StackTuringMachine.lean:490-494`). -/
private theorem shiStep_dispatch (tm₁ tm₂ : Turing.FinTM2) [DecidableEq tm₁.K]
    [DecidableEq (CompK tm₁ tm₂)] (tr : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (dflt : tm₂.Γ tm₂.k₀) (T : ∀ k, List (CompΓ tm₁ tm₂ k)) (w₂ : tm₂.σ)
    (r : Option (tm₂.Γ tm₂.k₀)) (l : tm₁.Λ) (v : tm₁.σ) (S : ∀ i, List (tm₁.Γ i)) :
    step (compM tm₁ tm₂ tr dflt)
        (⟨Option.some (injΛ₁ tm₁ tm₂ l), ((v, w₂, r) : Compσ tm₁ tm₂),
          liftStk₁ tm₁ tm₂ T S⟩ : CompCfg tm₁ tm₂)
      = Option.some (stepAux (trStmt₁ tm₁ tm₂ (tm₁.m l)) ((v, w₂, r) : Compσ tm₁ tm₂)
          (liftStk₁ tm₁ tm₂ T S)) := by
  first
  | (rfl
     done)
  | (simp only [step, compM, injΛ₁]
     done)
  | (simp only [Turing.TM2.step.eq_2, compM, injΛ₁]
     done)

/-- **One composite step is the lift of one component step**, in explicit form. -/
private theorem shiStep_step_explicit (tm₁ tm₂ : Turing.FinTM2) [DecidableEq tm₁.K]
    [DecidableEq (CompK tm₁ tm₂)] (tr : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (dflt : tm₂.Γ tm₂.k₀) (T : ∀ k, List (CompΓ tm₁ tm₂ k)) (w₂ : tm₂.σ)
    (r : Option (tm₂.Γ tm₂.k₀)) (l : tm₁.Λ) (v : tm₁.σ) (S : ∀ i, List (tm₁.Γ i)) :
    step (compM tm₁ tm₂ tr dflt)
        (⟨Option.some (injΛ₁ tm₁ tm₂ l), ((v, w₂, r) : Compσ tm₁ tm₂),
          liftStk₁ tm₁ tm₂ T S⟩ : CompCfg tm₁ tm₂)
      = Option.some (liftCfg₁ tm₁ tm₂ T w₂ r (stepAux (tm₁.m l) v S)) := by
  have H := ShiTM.stepAux_trStmt_one_simulation tm₁ tm₂ T
  have hsim := H.1 (tm₁.m l) ((v, w₂, r) : Compσ tm₁ tm₂) S
  first
  | (rw [shiStep_dispatch tm₁ tm₂ tr dflt T w₂ r l v S, hsim]
     done)
  | (rw [shiStep_dispatch tm₁ tm₂ tr dflt T w₂ r l v S, hsim]
     rfl
     done)
  | (rw [shiStep_dispatch tm₁ tm₂ tr dflt T w₂ r l v S]
     exact congrArg Option.some hsim
     done)
  | (exact congrArg Option.some hsim
     done)

/-- One composite step, in the `liftCfg₁`/`Option.map` form used by the iteration below. -/
private theorem shiStep_step_lift (tm₁ tm₂ : Turing.FinTM2) [DecidableEq tm₁.K]
    [DecidableEq (CompK tm₁ tm₂)] (tr : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (dflt : tm₂.Γ tm₂.k₀) (T : ∀ k, List (CompΓ tm₁ tm₂ k)) (w₂ : tm₂.σ)
    (r : Option (tm₂.Γ tm₂.k₀)) (l : tm₁.Λ) (v : tm₁.σ) (S : ∀ i, List (tm₁.Γ i)) :
    step (compM tm₁ tm₂ tr dflt) (liftCfg₁ tm₁ tm₂ T w₂ r ⟨Option.some l, v, S⟩)
      = (step tm₁.m (⟨Option.some l, v, S⟩ : Cfg tm₁.Γ tm₁.Λ tm₁.σ)).map
          (liftCfg₁ tm₁ tm₂ T w₂ r) := by
  have hexp := shiStep_step_explicit tm₁ tm₂ tr dflt T w₂ r l v S
  first
  | (rw [shiStep_liftCfg1_some tm₁ tm₂ T w₂ r l v S, hexp]
     done)
  | (rw [shiStep_liftCfg1_some tm₁ tm₂ T w₂ r l v S, hexp]
     rfl
     done)
  | (exact hexp
     done)
  | (rw [shiStep_liftCfg1_some tm₁ tm₂ T w₂ r l v S, hexp]
     simp only [step, Option.map_some]
     done)

/-- **(a) One step of the composite machine at a first-component label.**

Fix `tm₁ tm₂ : Turing.FinTM2`, a symbol translation `tr` and dummy symbol `dflt` (the data
of `ShiTM2.comp`), a family `T` of background stacks (the second machine's stacks and the
scratch stack), a second-component state `w₂` and a transfer register `r`.  Then for every
first-component label `l`, state `v` and stack family `S`:

1. **dispatch**: one `Turing.TM2.step` of `ShiTM2.compM tm₁ tm₂ tr dflt` from the lifted
   configuration `⟨some (injΛ₁ tm₁ tm₂ l), (v, w₂, r), liftStk₁ tm₁ tm₂ T S⟩` is
   `some (stepAux (trStmt₁ tm₁ tm₂ (tm₁.m l)) (v, w₂, r) (liftStk₁ tm₁ tm₂ T S))` -- the
   composite really does run the translated program of the first component there;
2. and that is `some` of the `ShiTM2.liftCfg₁`-lift of the first component's own
   `stepAux (tm₁.m l) v S`: the component's stacks move as they do in its own run, the
   background stacks `T` are untouched, and `w₂`, `r` are unchanged;
3. equivalently, in `Option.map` form and with the source configuration itself written as a
   `liftCfg₁`, one composite step is the lift of one component
   `Turing.TM2.step` -- the form that iterates;
4. **goto leaf**: if the component's step lands on a label `some l'`, the composite lands
   on `some (injΛ₁ tm₁ tm₂ l')`, with the state and stacks lifted -- a plain relabelling;
5. **halt leaf**: if the component's step lands on `none`, where
   `Turing.TM2.step ⟨none, _, _⟩ = none` would make it dead and unresumable, the composite
   instead lands on `some (lcopyA tm₁ tm₂)`, the entry label of the copy phase, with the
   same lifted state and stacks;
6. consequently the composite is **never dead** after such a step: the resulting
   configuration always has a `some` label and can be sequenced after.  Conjuncts 5 and 6
   are the whole point of `ShiTM2.trStmt₁`.

Note that conjuncts 4 and 5 speak of the leaf actually *reached*, not of the top
constructor of `tm₁.m l`: `stepAux` recurses the entire `Stmt` tree inside one
`Turing.TM2.step`.

The two `DecidableEq` binders are structure fields of `Turing.FinTM2`, not instances;
`tm₁.kDecidableEq` and `ShiTM2.compKDecEq tm₁ tm₂` are the intended arguments. -/
private theorem shiStep_pack (tm₁ tm₂ : Turing.FinTM2) [DecidableEq tm₁.K]
    [DecidableEq (CompK tm₁ tm₂)] (tr : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (dflt : tm₂.Γ tm₂.k₀) (T : ∀ k, List (CompΓ tm₁ tm₂ k)) (w₂ : tm₂.σ)
    (r : Option (tm₂.Γ tm₂.k₀)) :
    (∀ (l : tm₁.Λ) (v : tm₁.σ) (S : ∀ i, List (tm₁.Γ i)),
        step (compM tm₁ tm₂ tr dflt)
            (⟨Option.some (injΛ₁ tm₁ tm₂ l), ((v, w₂, r) : Compσ tm₁ tm₂),
              liftStk₁ tm₁ tm₂ T S⟩ : CompCfg tm₁ tm₂)
          = Option.some (stepAux (trStmt₁ tm₁ tm₂ (tm₁.m l)) ((v, w₂, r) : Compσ tm₁ tm₂)
              (liftStk₁ tm₁ tm₂ T S)))
  ∧ (∀ (l : tm₁.Λ) (v : tm₁.σ) (S : ∀ i, List (tm₁.Γ i)),
        step (compM tm₁ tm₂ tr dflt)
            (⟨Option.some (injΛ₁ tm₁ tm₂ l), ((v, w₂, r) : Compσ tm₁ tm₂),
              liftStk₁ tm₁ tm₂ T S⟩ : CompCfg tm₁ tm₂)
          = Option.some (liftCfg₁ tm₁ tm₂ T w₂ r (stepAux (tm₁.m l) v S)))
  ∧ (∀ (l : tm₁.Λ) (v : tm₁.σ) (S : ∀ i, List (tm₁.Γ i)),
        step (compM tm₁ tm₂ tr dflt) (liftCfg₁ tm₁ tm₂ T w₂ r ⟨Option.some l, v, S⟩)
          = (step tm₁.m (⟨Option.some l, v, S⟩ : Cfg tm₁.Γ tm₁.Λ tm₁.σ)).map
              (liftCfg₁ tm₁ tm₂ T w₂ r))
  ∧ (∀ (l : tm₁.Λ) (v : tm₁.σ) (S : ∀ i, List (tm₁.Γ i)) (l' : tm₁.Λ),
        (stepAux (tm₁.m l) v S).l = Option.some l' →
        step (compM tm₁ tm₂ tr dflt)
            (⟨Option.some (injΛ₁ tm₁ tm₂ l), ((v, w₂, r) : Compσ tm₁ tm₂),
              liftStk₁ tm₁ tm₂ T S⟩ : CompCfg tm₁ tm₂)
          = Option.some (⟨Option.some (injΛ₁ tm₁ tm₂ l'),
              (((stepAux (tm₁.m l) v S).var, w₂, r) : Compσ tm₁ tm₂),
              liftStk₁ tm₁ tm₂ T (stepAux (tm₁.m l) v S).stk⟩ : CompCfg tm₁ tm₂))
  ∧ (∀ (l : tm₁.Λ) (v : tm₁.σ) (S : ∀ i, List (tm₁.Γ i)),
        (stepAux (tm₁.m l) v S).l = Option.none →
        step (compM tm₁ tm₂ tr dflt)
            (⟨Option.some (injΛ₁ tm₁ tm₂ l), ((v, w₂, r) : Compσ tm₁ tm₂),
              liftStk₁ tm₁ tm₂ T S⟩ : CompCfg tm₁ tm₂)
          = Option.some (⟨Option.some (lcopyA tm₁ tm₂),
              (((stepAux (tm₁.m l) v S).var, w₂, r) : Compσ tm₁ tm₂),
              liftStk₁ tm₁ tm₂ T (stepAux (tm₁.m l) v S).stk⟩ : CompCfg tm₁ tm₂))
  ∧ (∀ (l : tm₁.Λ) (v : tm₁.σ) (S : ∀ i, List (tm₁.Γ i)),
        ∃ c : CompCfg tm₁ tm₂,
          step (compM tm₁ tm₂ tr dflt)
              (⟨Option.some (injΛ₁ tm₁ tm₂ l), ((v, w₂, r) : Compσ tm₁ tm₂),
                liftStk₁ tm₁ tm₂ T S⟩ : CompCfg tm₁ tm₂) = Option.some c
        ∧ c.l ≠ Option.none) := by
  refine ⟨fun l v S => shiStep_dispatch tm₁ tm₂ tr dflt T w₂ r l v S,
    fun l v S => shiStep_step_explicit tm₁ tm₂ tr dflt T w₂ r l v S,
    fun l v S => shiStep_step_lift tm₁ tm₂ tr dflt T w₂ r l v S,
    fun l v S l' hl => ?_, fun l v S hl => ?_, fun l v S => ?_⟩
  · first
    | (rw [shiStep_step_explicit tm₁ tm₂ tr dflt T w₂ r l v S, liftCfg₁, hl]
       done)
    | (rw [shiStep_step_explicit tm₁ tm₂ tr dflt T w₂ r l v S]
       simp only [liftCfg₁, hl, Option.elim_some]
       done)
    | (rw [shiStep_step_explicit tm₁ tm₂ tr dflt T w₂ r l v S]
       unfold liftCfg₁
       rw [hl]
       done)
    | (rw [shiStep_step_explicit tm₁ tm₂ tr dflt T w₂ r l v S]
       unfold liftCfg₁
       simp only [hl, Option.elim_some]
       done)
    | (rw [shiStep_step_explicit tm₁ tm₂ tr dflt T w₂ r l v S]
       congr 1
       unfold liftCfg₁
       simp only [hl, Option.elim_some]
       done)
  · first
    | (rw [shiStep_step_explicit tm₁ tm₂ tr dflt T w₂ r l v S, liftCfg₁, hl]
       done)
    | (rw [shiStep_step_explicit tm₁ tm₂ tr dflt T w₂ r l v S]
       simp only [liftCfg₁, hl, Option.elim_none]
       done)
    | (rw [shiStep_step_explicit tm₁ tm₂ tr dflt T w₂ r l v S]
       unfold liftCfg₁
       rw [hl]
       done)
    | (rw [shiStep_step_explicit tm₁ tm₂ tr dflt T w₂ r l v S]
       unfold liftCfg₁
       simp only [hl, Option.elim_none]
       done)
    | (rw [shiStep_step_explicit tm₁ tm₂ tr dflt T w₂ r l v S]
       congr 1
       unfold liftCfg₁
       simp only [hl, Option.elim_none]
       done)
  · refine ⟨liftCfg₁ tm₁ tm₂ T w₂ r (stepAux (tm₁.m l) v S),
      shiStep_step_explicit tm₁ tm₂ tr dflt T w₂ r l v S, ?_⟩
    first
    | (exact Option.some_ne_none _
       done)
    | (simp only [liftCfg₁]
       exact Option.some_ne_none _
       done)
    | (simp [liftCfg₁]
       done)

/-! ### (b) The step-exact iteration -/

/-- The iteration, by induction on `n`, peeling the **last** step.  `l`, `v`, `S` are fixed
throughout: peeling from the back leaves the start configuration alone, so only liveness at
`j = n` is consumed in the induction step. -/
private theorem shiStep_iterate (tm₁ tm₂ : Turing.FinTM2) [DecidableEq tm₁.K]
    [DecidableEq (CompK tm₁ tm₂)] (tr : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (dflt : tm₂.Γ tm₂.k₀) (T : ∀ k, List (CompΓ tm₁ tm₂ k)) (w₂ : tm₂.σ)
    (r : Option (tm₂.Γ tm₂.k₀)) (l : tm₁.Λ) (v : tm₁.σ) (S : ∀ i, List (tm₁.Γ i)) :
    ∀ n : ℕ,
      (∀ j < n, ∃ (l' : tm₁.Λ) (v' : tm₁.σ) (S' : ∀ i, List (tm₁.Γ i)),
          (fun c : Option (Cfg tm₁.Γ tm₁.Λ tm₁.σ) => c.bind (step tm₁.m))^[j]
              (Option.some (⟨Option.some l, v, S⟩ : Cfg tm₁.Γ tm₁.Λ tm₁.σ))
            = Option.some (⟨Option.some l', v', S'⟩ : Cfg tm₁.Γ tm₁.Λ tm₁.σ)) →
      (fun c : Option (CompCfg tm₁ tm₂) => c.bind (step (compM tm₁ tm₂ tr dflt)))^[n]
          (Option.some (liftCfg₁ tm₁ tm₂ T w₂ r ⟨Option.some l, v, S⟩))
        = ((fun c : Option (Cfg tm₁.Γ tm₁.Λ tm₁.σ) => c.bind (step tm₁.m))^[n]
            (Option.some (⟨Option.some l, v, S⟩ : Cfg tm₁.Γ tm₁.Λ tm₁.σ))).map
              (liftCfg₁ tm₁ tm₂ T w₂ r) := by
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
    | (exact shiStep_step_lift tm₁ tm₂ tr dflt T w₂ r l' v' S'
       done)
    | (simp only [Option.map_some, Option.bind_some]
       exact shiStep_step_lift tm₁ tm₂ tr dflt T w₂ r l' v' S'
       done)
    | (simp only [Option.map_some, Option.bind_some,
         shiStep_step_lift tm₁ tm₂ tr dflt T w₂ r l' v' S']
       done)

/-- **(b) Step-exact iteration of the first component inside the composite.**

Suppose the first component, started at `⟨some l, v, S⟩`, stays **live for the first `n`
configurations**: for every `j < n` its `j`-th configuration exists and has a `some` label,
i.e. is of the form `⟨some l', v', S'⟩`.  Then:

1. the composite's `n`-fold iterate from the lifted start configuration
   `ShiTM2.liftCfg₁ tm₁ tm₂ T w₂ r ⟨some l, v, S⟩` is the `Option.map`-lift of the
   component's own `n`-fold iterate -- an equation between iterates of
   `fun c => c.bind (Turing.TM2.step _)`, which is the `evals_in_steps` field of
   `StateTransition.EvalsTo`;
2. hence if the component reaches a configuration `c` in **exactly** `n` steps, the
   composite reaches `ShiTM2.liftCfg₁ tm₁ tm₂ T w₂ r c` in exactly `n` steps, packaged as
   `StateTransition.EvalsToInTime ... n`, ready to be chained with
   `StateTransition.EvalsToInTime.trans` -- in the assembly, with the copy phase supplied
   by `ShiTM.copy_loop_transfers_stack`.

The liveness hypothesis is necessary, not cosmetic: a component that halts at step `j < n`
has `none` as its `(j+1)`-st configuration, while the composite continues from
`ShiTM2.lcopyA` into the copy phase, so the two runs diverge exactly there.  Its `j = 0`
instance is trivially satisfiable (`l' := l`, `v' := v`, `S' := S`), and liveness at `j`
already implies that the `(j+1)`-st configuration exists, so the hypothesis constrains
labels only. -/
theorem solution (tm₁ tm₂ : Turing.FinTM2) [DecidableEq tm₁.K]
    [DecidableEq (CompK tm₁ tm₂)] (tr : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (dflt : tm₂.Γ tm₂.k₀) (T : ∀ k, List (CompΓ tm₁ tm₂ k)) (w₂ : tm₂.σ)
    (r : Option (tm₂.Γ tm₂.k₀)) (n : ℕ) (l : tm₁.Λ) (v : tm₁.σ)
    (S : ∀ i, List (tm₁.Γ i))
    (hlive : ∀ j < n, ∃ (l' : tm₁.Λ) (v' : tm₁.σ) (S' : ∀ i, List (tm₁.Γ i)),
        (fun c : Option (Cfg tm₁.Γ tm₁.Λ tm₁.σ) => c.bind (step tm₁.m))^[j]
            (Option.some (⟨Option.some l, v, S⟩ : Cfg tm₁.Γ tm₁.Λ tm₁.σ))
          = Option.some (⟨Option.some l', v', S'⟩ : Cfg tm₁.Γ tm₁.Λ tm₁.σ)) :
    (fun c : Option (CompCfg tm₁ tm₂) => c.bind (step (compM tm₁ tm₂ tr dflt)))^[n]
        (Option.some (liftCfg₁ tm₁ tm₂ T w₂ r ⟨Option.some l, v, S⟩))
      = ((fun c : Option (Cfg tm₁.Γ tm₁.Λ tm₁.σ) => c.bind (step tm₁.m))^[n]
          (Option.some (⟨Option.some l, v, S⟩ : Cfg tm₁.Γ tm₁.Λ tm₁.σ))).map
            (liftCfg₁ tm₁ tm₂ T w₂ r)
  ∧ (∀ c : Cfg tm₁.Γ tm₁.Λ tm₁.σ,
        (fun c : Option (Cfg tm₁.Γ tm₁.Λ tm₁.σ) => c.bind (step tm₁.m))^[n]
            (Option.some (⟨Option.some l, v, S⟩ : Cfg tm₁.Γ tm₁.Λ tm₁.σ))
          = Option.some c →
        Nonempty (StateTransition.EvalsToInTime (step (compM tm₁ tm₂ tr dflt))
          (liftCfg₁ tm₁ tm₂ T w₂ r ⟨Option.some l, v, S⟩)
          (Option.some (liftCfg₁ tm₁ tm₂ T w₂ r c)) n)) := by
  have hkey := shiStep_iterate tm₁ tm₂ tr dflt T w₂ r l v S n hlive
  refine ⟨hkey, fun c hc => ?_⟩
  rw [hc] at hkey
  have hkey' : (fun c : Option (CompCfg tm₁ tm₂) =>
      c.bind (step (compM tm₁ tm₂ tr dflt)))^[n]
        (Option.some (liftCfg₁ tm₁ tm₂ T w₂ r ⟨Option.some l, v, S⟩))
      = Option.some (liftCfg₁ tm₁ tm₂ T w₂ r c) := by
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
