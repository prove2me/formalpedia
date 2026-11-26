-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.sumsetCardLowerBound_of_add_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:07:17.160544+00:00
-- url     : https://prove2.me/submissions/36558c85-030f-4687-a941-33845317852d

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
theorem _root_.solution (h : m + d ≤ n + 1) :
    sumsetCardLowerBound d m n = n + d * (m - 1) := by
  rw [sumsetCardLowerBound_eq, sum_const_nat (m := d) (by grind), Nat.card_Icc]
  grind
end SumOfSetsInSeveralDimensions
