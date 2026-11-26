-- Prove2me | solution 1 for TranslationOuter.birthday_paradox_of_high_good_plan_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:14:53.021636+00:00
-- url     : https://prove2.me/submissions/1f78d3f2-ab86-46c1-8af5-73ff9449354f

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_GeneralFinalRatio_quantitative_to_epsilon
public import Theorems.Thm_TranslationOuter_quantitative_bound_of_high_good_plan_card_bound

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
            Nat.card (RotationSystem d V))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
        IsRegularOfDegree G d →
        ∀ (k : ℕ) (start : OrientedEdge G),
          C * Real.sqrt (Fintype.card V : ℝ) < (k : ℝ) →
            simpleProbability G start k < ε := by
  have hquant :
      ∀ {V : Type u} [Fintype V]
          (G : SimpleGraph V), IsRegularOfDegree G d →
          ∀ (k : ℕ) (start : OrientedEdge G), 0 < k →
            simpleProbability G start k ≤
              (K d : ℝ) * (Fintype.card V : ℝ) / (k : ℝ) ^ 2 := by
    exact quantitative_bound_of_high_good_plan_card_bound d hd hcard
  obtain ⟨C, hC, hconvert⟩ := quantitative_to_epsilon d hd ε hε
  refine ⟨C, hC, ?_⟩
  intro V instV G hG k start hthreshold
  exact hconvert (Fintype.card V) k (simpleProbability G start k)
    (hquant G hG k start (by
      have hsqrt : 0 ≤ Real.sqrt (Fintype.card V : ℝ) := Real.sqrt_nonneg _
      have hkreal : (0 : ℝ) < k :=
        lt_of_le_of_lt (mul_nonneg hC.le hsqrt) hthreshold
      exact_mod_cast hkreal))
    hthreshold
end TranslationOuter
