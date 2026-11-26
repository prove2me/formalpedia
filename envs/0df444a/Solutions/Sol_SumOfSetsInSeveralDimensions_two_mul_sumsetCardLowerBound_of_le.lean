-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.two_mul_sumsetCardLowerBound_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:10:56.734494+00:00
-- url     : https://prove2.me/submissions/61307ac1-3f94-4169-bf17-d119641bc2b1

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBoundFunction
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBoundValues
public import Theorems.Thm_SumOfSetsInSeveralDimensions_sumsetCardLowerBound_add_one
public import Theorems.Thm_SumOfSetsInSeveralDimensions_sumsetCardLowerBound_eq


set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
variable {d m n : ℕ}
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution (hm : 1 ≤ m) (hmn : m ≤ n) (hnd : n ≤ d) :
    2 * sumsetCardLowerBound d m n = 2 * n + (m - 1) * (2 * n - m) := by
  induction m, hm using Nat.le_induction with
  | base => simp [sumsetCardLowerBound_eq]
  | succ m hm ih =>
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_lt hmn
    rw [sumsetCardLowerBound_add_one hm, (by grind : min d (m + t + 1 - m) = t + 1),
      Nat.add_sub_cancel, (by grind : 2 * (m + t + 1) - (m + 1) = m + 2 * t + 1)]
    rw [(by grind : 2 * (m + t + 1) - m = m + 2 * t + 2)] at ih
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
    rw [Nat.add_sub_cancel] at ih
    nlinarith [ih (by grind)]
end SumOfSetsInSeveralDimensions
