-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.sum_weightedNeighborSum_centeredVertexIndicator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:44:05.514422+00:00
-- url     : https://prove2.me/submissions/6a899188-edc7-4416-947e-cfc4dc59824e

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Mathlib.Data.Nat.Log
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Theorems.Thm_QEC_Coding_SmallSetExpansion_sum_centeredVertexIndicator

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
theorem _root_.solution
    [Fintype V] [DecidableEq V]
    (M : WeightedGraph V) (degree : Nat)
    (hSymm : IsSymmetric M) (hRegular : IsRegular M degree)
    (T : Finset V) :
    ∑ v, weightedNeighborSum M (centeredVertexIndicator T) v = 0 := by
  classical
  rw [show
      (∑ v, weightedNeighborSum M (centeredVertexIndicator T) v) =
        ∑ u, centeredVertexIndicator T u * ∑ v, (M u v : ℝ) by
    unfold weightedNeighborSum
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _hu
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _hv
    rw [hSymm]
    ring]
  have hDegree (u : V) : (∑ v, (M u v : ℝ)) = degree := by
    exact_mod_cast hRegular u
  simp_rw [hDegree, ← Finset.sum_mul]
  rw [sum_centeredVertexIndicator, zero_mul]
end QEC.Coding.SmallSetExpansion
