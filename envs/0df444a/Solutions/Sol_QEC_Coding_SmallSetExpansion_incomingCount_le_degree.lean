-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.incomingCount_le_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:46:02.871171+00:00
-- url     : https://prove2.me/submissions/79e52fac-2353-433c-993f-e11e58f5a1b7

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Mathlib.Data.Nat.Log
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
theorem _root_.solution
    [Fintype V] [DecidableEq V]
    (M : WeightedGraph V) (degree : Nat)
    (hSymm : IsSymmetric M) (hRegular : IsRegular M degree)
    (S : Finset V) (x : V) :
    incomingCount M S x ≤ degree := by
  calc
    incomingCount M S x = ∑ v ∈ S, M x v := by
      unfold incomingCount
      apply Finset.sum_congr rfl
      intro v _hv
      exact hSymm v x
    _ ≤ ∑ v, M x v := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun _ _ _ => Nat.zero_le _)
    _ = degree := hRegular x
end QEC.Coding.SmallSetExpansion
