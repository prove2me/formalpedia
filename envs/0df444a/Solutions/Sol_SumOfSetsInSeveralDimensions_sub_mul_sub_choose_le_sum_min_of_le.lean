-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.sub_mul_sub_choose_le_sum_min_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:10:39.906896+00:00
-- url     : https://prove2.me/submissions/62f3dd76-43cd-44f1-8f5a-93bef5344d7a

module
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Definitions.Def_SumOfSetsInSeveralDimensions_FreimanDimension
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.Linarith
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDimSumset
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBound
public import Definitions.Def_SumOfSetsInSeveralDimensions_FreimanDimensionSumsetBounds
public import Theorems.Thm_SumOfSetsInSeveralDimensions_sub_mul_sub_choose_le_sum_min

set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
noncomputable section
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution {a b r d : ℕ} (hba : b ≤ a) (hrd : r ≤ d + 1) :
    (r - 1) * b - (r + 1).choose 2 ≤ ∑ t ∈ Icc 1 (b - 1), min d (a - t) := by
  refine (sub_mul_sub_choose_le_sum_min b r).trans ?_
  apply sum_le_sum
  grind
end SumOfSetsInSeveralDimensions
