-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.crossCount_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:45:32.891383+00:00
-- url     : https://prove2.me/submissions/34f10e6f-23a2-45d6-9133-830ed90024c6

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Mathlib.Data.Nat.Log
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
theorem _root_.solution [Fintype V]
    (M : WeightedGraph V) (S T : Finset V) :
    crossCount (square M) S T =
      ∑ x, incomingCount M S x * outgoingCount M T x := by
  simp only [crossCount, square, incomingCount, outgoingCount]
  calc
    (∑ v ∈ S, ∑ u ∈ T, ∑ x, M v x * M x u) =
        ∑ v ∈ S, ∑ x, ∑ u ∈ T, M v x * M x u := by
      apply Finset.sum_congr rfl
      intro v _hv
      exact Finset.sum_comm
    _ = ∑ x, ∑ v ∈ S, ∑ u ∈ T, M v x * M x u :=
      Finset.sum_comm
    _ = ∑ x, (∑ v ∈ S, M v x) * ∑ u ∈ T, M x u := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro v _hv
      rw [Finset.mul_sum]
end QEC.Coding.SmallSetExpansion
