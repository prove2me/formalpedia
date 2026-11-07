-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.adjacencyPairing_centeredVertexIndicator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:44:56.906453+00:00
-- url     : https://prove2.me/submissions/2573e119-0786-407e-81f8-e8cbb2853581

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Mathlib.Data.Nat.Log
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Theorems.Thm_QEC_Coding_SmallSetExpansion_sum_centeredVertexIndicator_mul
import Theorems.Thm_QEC_Coding_SmallSetExpansion_weightedNeighborSum_centeredVertexIndicator
import Theorems.Thm_QEC_Coding_SmallSetExpansion_sum_weightedNeighborSum_centeredVertexIndicator

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
theorem _root_.solution
    [Fintype V] [DecidableEq V]
    (M : WeightedGraph V) (degree : Nat)
    (hSymm : IsSymmetric M) (hRegular : IsRegular M degree)
    (S T : Finset V) :
    adjacencyPairing M
        (centeredVertexIndicator S) (centeredVertexIndicator T) =
      (Fintype.card V : ℝ) *
        ((Fintype.card V : ℝ) * crossCount M S T -
          degree * (S.card : ℝ) * T.card) := by
  classical
  rw [adjacencyPairing]
  change (∑ v, centeredVertexIndicator S v *
      weightedNeighborSum M (centeredVertexIndicator T) v) = _
  rw [sum_centeredVertexIndicator_mul]
  rw [sum_weightedNeighborSum_centeredVertexIndicator
    M degree hSymm hRegular T, mul_zero, sub_zero]
  simp_rw [weightedNeighborSum_centeredVertexIndicator
    M degree hRegular T]
  rw [Finset.sum_sub_distrib]
  simp_rw [← Finset.mul_sum]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hCross :
      (∑ v ∈ S, ∑ u ∈ T, (M v u : ℝ)) =
        crossCount M S T := by
    norm_cast
  rw [hCross]
  ring
end QEC.Coding.SmallSetExpansion
