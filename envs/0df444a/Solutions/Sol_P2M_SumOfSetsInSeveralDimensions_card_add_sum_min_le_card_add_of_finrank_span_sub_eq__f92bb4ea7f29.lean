-- Prove2me | solution 1 for P2M_SumOfSetsInSeveralDimensions_card_add_sum_min_le_card_add_of_finrank_span_sub_eq__f92bb4ea7f29
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:11:52.385801+00:00
-- url     : https://prove2.me/submissions/0e635cc2-a091-4a15-b3e2-986a71b91f84

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_ClosedForm
public import Definitions.Def_SumOfSetsInSeveralDimensions_FreimanDimensionSumsetBounds
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBound
public import Definitions.Def_SumOfSetsInSeveralDimensions_MinCardAdd
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_SumOfSetsInSeveralDimensions_Solution
public import Theorems.Thm_SumOfSetsInSeveralDimensions_card_add_sum_min_le_card_add_of_finrank_span_sub_eq


set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped Pointwise
open SumOfSetsInSeveralDimensions
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution {D d : ℕ}
    {A B : Finset (Fin D → ℝ)} (hB : B.Nonempty) (hBA : #B ≤ #A)
    (hdim : Module.finrank ℝ (Submodule.span ℝ (↑(A + B) - ↑(A + B) : Set (Fin D → ℝ))) = d) :
    #A + ∑ t ∈ Icc 1 (#B - 1), min d (#A - t) ≤ #(A + B) :=
  card_add_sum_min_le_card_add_of_finrank_span_sub_eq hB hBA hdim
end SumOfSetsInSeveralDimensions
