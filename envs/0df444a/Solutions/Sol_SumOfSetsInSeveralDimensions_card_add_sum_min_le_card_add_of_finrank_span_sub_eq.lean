-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.card_add_sum_min_le_card_add_of_finrank_span_sub_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:11:13.07192+00:00
-- url     : https://prove2.me/submissions/95ed4cc8-eea8-4adc-8f70-32882f39cdd4

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
public import Theorems.Thm_Finset_affineDim_eq_finrank_span_sub


set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution {D d : ℕ}
    {A B : Finset (Fin D → ℝ)} (hB : B.Nonempty) (hBA : #B ≤ #A)
    (hdim : Module.finrank ℝ (Submodule.span ℝ (↑(A + B) - ↑(A + B) : Set (Fin D → ℝ))) = d) :
    #A + ∑ t ∈ Icc 1 (#B - 1), min d (#A - t) ≤ #(A + B) :=
  card_add_sum_min_le_card_add hB hBA ((affineDim_eq_finrank_span_sub _).trans hdim)
end SumOfSetsInSeveralDimensions
