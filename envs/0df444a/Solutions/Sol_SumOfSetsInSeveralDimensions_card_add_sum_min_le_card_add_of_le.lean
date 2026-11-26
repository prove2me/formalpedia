-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.card_add_sum_min_le_card_add_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:11:10.541695+00:00
-- url     : https://prove2.me/submissions/ba58d18d-d51a-4753-a5e8-27f2d9447cd0

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_SumOfSetsInSeveralDimensions_GeometricDeletion
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBoundFunction
public import Definitions.Def_SumOfSetsInSeveralDimensions_Normalize
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBound
public import Theorems.Thm_SumOfSetsInSeveralDimensions_card_add_sum_min_le_card_add

set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution {D d : ℕ} {A B : Finset (Fin D → ℝ)}
    (hB : B.Nonempty) (hBA : #B ≤ #A) (hd : d ≤ (A + B).affineDim) :
    #A + ∑ t ∈ Icc 1 (#B - 1), min d (#A - t) ≤ #(A + B) := by
  refine le_trans ?_ (card_add_sum_min_le_card_add hB hBA rfl)
  gcongr
end SumOfSetsInSeveralDimensions
