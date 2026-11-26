-- Prove2me | solution 1 for TranslationOuter.quantitative_bound_of_high_good_plan_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:14:13.065965+00:00
-- url     : https://prove2.me/submissions/37591072-1f44-4037-acfd-7259734d4d16

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_natCard_rotationSystem
public import Theorems.Thm_simpleProbability_eq_goodRatio
public import Theorems.Thm_GeneralFinalRatio_ratio_bound
public import Theorems.Thm_GeneralFinalRatio_ratio_bound_of_high
public import Theorems.Thm_TranslationOuter_simpleWalkCount_eq_zero_of_card_le
public import Theorems.Thm_TranslationOuter_simpleProbability_le_one
public import Theorems.Thm_TranslationOuter_final_card_bound_from_k

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
open TranslationOuter
open GeneralFinalRatio
noncomputable section
universe u
namespace TranslationOuter
theorem _root_.solution
    (d : ℕ) [NeZero d] (hd : 3 ≤ d)
    (hcard :
      ∀ {V : Type u} [Fintype V]
          (G : SimpleGraph V) (hG : IsRegularOfDegree G d)
          (k : ℕ) (start : OrientedEdge G),
        0 < k →
        k < Fintype.card V →
        K d * Fintype.card V ≤ k ^ 2 →
        k * Nat.card (GoodOmega d G hG start k) ≤
          8 * (d - 1) * cutoff d (Fintype.card V) k *
            Nat.card (RotationSystem d V)) :
    ∀ {V : Type u} [Fintype V]
        (G : SimpleGraph V), IsRegularOfDegree G d →
        ∀ (k : ℕ) (start : OrientedEdge G), 0 < k →
          simpleProbability G start k ≤
            (K d : ℝ) * (Fintype.card V : ℝ) / (k : ℝ) ^ 2 := by
  intro V instV G hG k start hk
  by_cases hnk : Fintype.card V ≤ k
  · have hsimple := simpleWalkCount_eq_zero_of_card_le G start k hnk
    rw [simpleProbability, hsimple]
    norm_num
    positivity
  · have hkn : k < Fintype.card V := Nat.lt_of_not_ge hnk
    rw [simpleProbability_eq_goodRatio d hd G hG start k hk hkn]
    apply ratio_bound_of_high d (Fintype.card V) k _ hk
    · rw [← simpleProbability_eq_goodRatio d hd G hG start k hk hkn]
      exact simpleProbability_le_one d hd G hG start k hk
    · intro hhigh
      have hplans : 0 < Nat.card (RotationSystem d V) := by
        rw [natCard_rotationSystem]
        exact pow_pos (by omega) _
      apply ratio_bound d (Fintype.card V) k
        (Nat.card (GoodOmega d G hG start k))
        (Nat.card (RotationSystem d V)) hk hplans
      apply final_card_bound_from_k d (Fintype.card V) k
        (Nat.card (GoodOmega d G hG start k))
        (Nat.card (RotationSystem d V)) hd hkn
      exact hcard G hG k start hk hkn hhigh
end TranslationOuter
