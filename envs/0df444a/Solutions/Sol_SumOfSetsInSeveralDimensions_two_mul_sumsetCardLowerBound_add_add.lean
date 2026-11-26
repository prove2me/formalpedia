-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.two_mul_sumsetCardLowerBound_add_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:07:54.643206+00:00
-- url     : https://prove2.me/submissions/5e8cd8e4-a513-44f7-94e6-642a8117a16f

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBoundFunction
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBoundValues
public import Theorems.Thm_SumOfSetsInSeveralDimensions_sumsetCardLowerBound_add_one
public import Theorems.Thm_SumOfSetsInSeveralDimensions_sumsetCardLowerBound_of_add_le

set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
variable {d m n : ℕ}
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution (hmn : m ≤ n) (hnm : n < m + d) (hdn : d < n) :
    2 * sumsetCardLowerBound d m n + d * (d + 1) + (n - m) * (n - m + 1) = 2 * n * (d + 1) := by
  induction m, (by grind : n + 1 - d ≤ m) using Nat.le_induction with
  | base =>
    rw [sumsetCardLowerBound_of_add_le (by grind)]
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hdn
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le' (by grind : 1 ≤ d)
    rw [(by grind : e + 1 + c + 1 + 1 - (e + 1) - 1 = c + 1),
      (by grind : e + 1 + c + 1 - (e + 1 + c + 1 + 1 - (e + 1)) = e)]
    ring
  | succ m hm ih =>
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_lt hmn
    rw [sumsetCardLowerBound_add_one (by grind), (by grind : m + t + 1 - (m + 1) = t),
      (by grind : min d (m + t + 1 - m) = t + 1)]
    rw [(by grind : m + t + 1 - m = t + 1)] at ih
    nlinarith [ih (by grind) (by grind)]
end SumOfSetsInSeveralDimensions
