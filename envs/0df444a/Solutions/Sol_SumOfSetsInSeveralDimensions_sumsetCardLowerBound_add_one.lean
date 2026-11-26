-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.sumsetCardLowerBound_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:07:15.48073+00:00
-- url     : https://prove2.me/submissions/6468a206-4bd7-44b0-8c52-2b8e7a398d93

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBoundFunction
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBoundValues
public import Theorems.Thm_SumOfSetsInSeveralDimensions_sumsetCardLowerBound_eq


set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
variable {d m n : ℕ}
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution (hm : 1 ≤ m) :
    sumsetCardLowerBound d (m + 1) n = sumsetCardLowerBound d m n + min d (n - m) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  rw [sumsetCardLowerBound_eq, sumsetCardLowerBound_eq, Nat.add_sub_cancel, Nat.add_sub_cancel,
    sum_Icc_succ_top (by grind)]
  grind
end SumOfSetsInSeveralDimensions
