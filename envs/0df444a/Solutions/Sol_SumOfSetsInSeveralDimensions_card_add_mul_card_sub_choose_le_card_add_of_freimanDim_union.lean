-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.card_add_mul_card_sub_choose_le_card_add_of_freimanDim_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:13:05.371961+00:00
-- url     : https://prove2.me/submissions/6d86122d-dbb0-4875-92a7-fb3733bfbd6d

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
public import Theorems.Thm_SumOfSetsInSeveralDimensions_sub_mul_sub_choose_le_sum_min_of_le
public import Theorems.Thm_SumOfSetsInSeveralDimensions_card_add_sum_min_le_of_freimanDim_union

set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
noncomputable section
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution
    {G : Type*} [DecidableEq G] [AddCommMonoid G] {r : ℕ} {A B : Finset G} (hr : 1 ≤ r)
    (hB : B.Nonempty) (hBA : #B ≤ #A) (hdim : freimanDim (A ∪ B) = r) :
    #A + (r - 1) * #B - (r + 1).choose 2 ≤ #(A + B) := by
  grind [card_add_sum_min_le_of_freimanDim_union hr hB hBA hdim,
    sub_mul_sub_choose_le_sum_min_of_le (r := r) (d := r - 1) hBA (by grind)]
end SumOfSetsInSeveralDimensions
