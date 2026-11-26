-- Prove2me | solution 1 for P2M_SumOfSetsInSeveralDimensions_card_add_mul_card_le_card_add_add_of_le_finrank_span_sub__e0ebb9409f0f
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:13:33.479263+00:00
-- url     : https://prove2.me/submissions/12169872-2898-4486-ad7b-ca19444dcf12

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_ClosedForm
public import Definitions.Def_SumOfSetsInSeveralDimensions_FreimanDimensionSumsetBounds
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBound
public import Definitions.Def_SumOfSetsInSeveralDimensions_MinCardAdd
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_SumOfSetsInSeveralDimensions_Solution
public import Theorems.Thm_SumOfSetsInSeveralDimensions_card_add_mul_card_le_card_add_add_of_le_finrank_span_sub


set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped Pointwise
open SumOfSetsInSeveralDimensions
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution {D d : ℕ}
    {A B : Finset (Fin D → ℝ)} (hB : B.Nonempty) (hBA : #B ≤ #A)
    (hd : d ≤ Module.finrank ℝ (Submodule.span ℝ (↑(A + B) - ↑(A + B) : Set (Fin D → ℝ)))) :
    #A + d * #B ≤ #(A + B) + d * (d + 1) / 2 :=
  card_add_mul_card_le_card_add_add_of_le_finrank_span_sub hB hBA hd
end SumOfSetsInSeveralDimensions
