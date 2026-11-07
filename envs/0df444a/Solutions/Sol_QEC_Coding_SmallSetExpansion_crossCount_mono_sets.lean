-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.crossCount_mono_sets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:45:13.772072+00:00
-- url     : https://prove2.me/submissions/38e04e6b-cc7b-408b-9cd4-40cd50efd1e1

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Mathlib.Data.Nat.Log
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
theorem _root_.solution [DecidableEq V]
    (M : WeightedGraph V) {S S' T T' : Finset V}
    (hS : S ⊆ S') (hT : T ⊆ T') :
    crossCount M S T ≤ crossCount M S' T' := by
  unfold crossCount
  calc
    (∑ v ∈ S, ∑ u ∈ T, M v u) ≤
        ∑ v ∈ S, ∑ u ∈ T', M v u := by
      apply Finset.sum_le_sum
      intro v _hv
      exact Finset.sum_le_sum_of_subset hT
    _ ≤ ∑ v ∈ S', ∑ u ∈ T', M v u :=
      Finset.sum_le_sum_of_subset hS
end QEC.Coding.SmallSetExpansion
