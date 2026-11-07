-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.crossCount_le_degree_mul_card_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:45:24.36303+00:00
-- url     : https://prove2.me/submissions/9f07c7f7-cd25-4056-8e75-ee94e823525e

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Mathlib.Data.Nat.Log
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
theorem _root_.solution [Fintype V] [DecidableEq V]
    (M : WeightedGraph V) (degree : Nat) (hRegular : IsRegular M degree)
    (S T : Finset V) :
    crossCount M S T ≤ degree * S.card := by
  unfold crossCount
  calc
    (∑ v ∈ S, ∑ u ∈ T, M v u) ≤
        ∑ v ∈ S, ∑ u, M v u := by
      apply Finset.sum_le_sum
      intro v _hv
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ T)
    _ = ∑ _v ∈ S, degree := by
      apply Finset.sum_congr rfl
      intro v _hv
      exact hRegular v
    _ = degree * S.card := by simp [Nat.mul_comm]
end QEC.Coding.SmallSetExpansion
