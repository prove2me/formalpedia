-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.card_intermediateSupport_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:46:06.867474+00:00
-- url     : https://prove2.me/submissions/ee37d4ae-f388-4791-a298-aee849346d8c

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
    (M : WeightedGraph V) (degree : Nat) (hRegular : IsRegular M degree)
    (S : Finset V) :
    (intermediateSupport M S).card ≤ degree * S.card := by
  let U := intermediateSupport M S
  calc
    U.card = ∑ _x ∈ U, 1 := by simp
    _ ≤ ∑ x ∈ U, incomingCount M S x := by
      apply Finset.sum_le_sum
      intro x hx
      have hxNe : incomingCount M S x ≠ 0 := (Finset.mem_filter.mp hx).2
      omega
    _ ≤ ∑ x, incomingCount M S x := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U)
        (fun _ _ _ => Nat.zero_le _)
    _ = degree * S.card := by
      unfold incomingCount
      rw [Finset.sum_comm]
      calc
        (∑ v ∈ S, ∑ x, M v x) = ∑ _v ∈ S, degree := by
          apply Finset.sum_congr rfl
          intro v _hv
          exact hRegular v
        _ = degree * S.card := by simp [Nat.mul_comm]
end QEC.Coding.SmallSetExpansion
