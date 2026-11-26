-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.two_mul_sumsetCardLowerBound_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:10:55.650623+00:00
-- url     : https://prove2.me/submissions/a52f4c20-a2e0-4fb6-be8c-05a2cb2e1b3c

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBoundFunction
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBoundValues
public import Theorems.Thm_SumOfSetsInSeveralDimensions_two_mul_sumsetCardLowerBound_add_add

set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
variable {d m n : ℕ}
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution (hmn : m ≤ n) (hnm : n < m + d) (hdn : d < n) :
    2 * sumsetCardLowerBound d m n + (d - (n - m)) * (d - (n - m) - 1) =
      2 * (n + d * (m - 1)) := by
  have h := two_mul_sumsetCardLowerBound_add_add hmn hnm hdn
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hmn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt (by grind : t < d)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' (by grind : 1 ≤ m)
  rw [Nat.add_sub_cancel_left] at h
  rw [Nat.add_sub_cancel_left, (by grind : t + k + 1 - t = k + 1), Nat.add_sub_cancel,
    Nat.add_sub_cancel]
  nlinarith [h]
end SumOfSetsInSeveralDimensions
