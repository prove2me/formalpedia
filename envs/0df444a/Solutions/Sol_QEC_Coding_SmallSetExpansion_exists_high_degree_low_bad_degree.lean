-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.exists_high_degree_low_bad_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:47:59.797531+00:00
-- url     : https://prove2.me/submissions/0b98ffd0-48b1-4fdb-bb0b-b353f6182cdb

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_DegreeSelection

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
namespace QEC.Coding.SmallSetExpansion
theorem _root_.solution
    {V : Type u} (T : Finset V) (hT : T.Nonempty) (useful bad : V → ℝ)
    (maximum threshold badAverage badCutoff : ℝ)
    (hMaximum : 0 < maximum) (hThreshold : 0 < threshold)
    (hCutoff : 0 ≤ badCutoff)
    (hUseful : ∀ v ∈ T, useful v ≤ maximum)
    (hBadNonnegative : ∀ v ∈ T, 0 ≤ bad v)
    (hUsefulAverage : 2 * threshold * T.card ≤ ∑ v ∈ T, useful v)
    (hBadAverage : (∑ v ∈ T, bad v) ≤ badAverage * T.card)
    (hBudgets : badAverage * maximum ≤ badCutoff * threshold) :
    ∃ v ∈ T, threshold ≤ useful v ∧ bad v ≤ badCutoff := by
  classical
  let high := T.filter fun v => threshold ≤ useful v
  have hHighSubset : high ⊆ T := Finset.filter_subset _ _
  have hUsefulUpper : (∑ v ∈ T, useful v) ≤
      threshold * T.card + maximum * high.card := by
    calc
      (∑ v ∈ T, useful v) ≤
          ∑ v ∈ T, (threshold + if threshold ≤ useful v then maximum else 0) := by
        apply Finset.sum_le_sum
        intro v hv
        by_cases h : threshold ≤ useful v
        · simp only [h, ite_true]
          linarith [hUseful v hv]
        · simp only [h, ite_false, add_zero]
          exact le_of_lt (lt_of_not_ge h)
      _ = threshold * T.card + maximum * high.card := by
        simp [high, Finset.sum_add_distrib, Finset.sum_ite, mul_comm]
  have hHighLower : threshold * T.card ≤ maximum * high.card := by
    linarith
  have hTCard : (0 : ℝ) < T.card := by exact_mod_cast Finset.card_pos.mpr hT
  have hHighNonempty : high.Nonempty := by
    apply Finset.card_pos.mp
    by_contra hn
    have hz : high.card = 0 := Nat.eq_zero_of_not_pos hn
    simp only [hz, Nat.cast_zero, mul_zero] at hHighLower
    exact (not_le_of_gt (mul_pos hThreshold hTCard)) hHighLower
  by_contra hNo
  have hBadHigh : ∀ v ∈ high, badCutoff < bad v := by
    intro v hv
    have hvData := Finset.mem_filter.mp hv
    by_contra h
    exact hNo ⟨v, hvData.1, hvData.2, le_of_not_gt h⟩
  have hBadStrict : badCutoff * high.card < ∑ v ∈ high, bad v := by
    calc
      badCutoff * high.card = ∑ _v ∈ high, badCutoff := by simp [mul_comm]
      _ < ∑ v ∈ high, bad v :=
        Finset.sum_lt_sum_of_nonempty hHighNonempty hBadHigh
  have hBadSumLe : (∑ v ∈ high, bad v) ≤ ∑ v ∈ T, bad v := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hHighSubset
    intro v hv _
    exact hBadNonnegative v hv
  have hBadCount : badCutoff * high.card < badAverage * T.card :=
    hBadStrict.trans_le (hBadSumLe.trans hBadAverage)
  have hScaledUseful := mul_le_mul_of_nonneg_left hHighLower hCutoff
  have hScaledBad := mul_lt_mul_of_pos_left hBadCount hMaximum
  have hScaledBudget := mul_le_mul_of_nonneg_right hBudgets hTCard.le
  nlinarith
end QEC.Coding.SmallSetExpansion
