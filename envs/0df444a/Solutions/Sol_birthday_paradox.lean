-- Prove2me | solution 1 for birthday_paradox
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:15:59.429213+00:00
-- url     : https://prove2.me/submissions/c678c28d-e431-4656-86a6-df25a3f33b3b

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_TranslationCollisionSwitching_high_switching_card_bound
public import Theorems.Thm_TranslationOuter_birthday_paradox_of_high_good_plan_card_bound

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false
universe u
theorem _root_.solution
    (d : ℕ) (hd : 3 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
        IsRegularOfDegree G d →
        ∀ (k : ℕ) (start : OrientedEdge G),
          C * Real.sqrt (Fintype.card V : ℝ) < (k : ℝ) →
            simpleProbability G start k < ε := by
  let : NeZero d := ⟨by omega⟩
  refine TranslationOuter.birthday_paradox_of_high_good_plan_card_bound d hd
    ?_ ε hε
  intro V instV G hG k start _hk hkn hhigh
  have hswitch := TranslationCollisionSwitching.high_switching_card_bound
    (d := d) G hG start k hd hhigh hkn
  simpa only [degreeCutoff, GeneralFinalRatio.cutoff, mul_comm, mul_left_comm,
    mul_assoc] using hswitch
