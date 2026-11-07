-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.sum_centeredVertexIndicator_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:43:08.753189+00:00
-- url     : https://prove2.me/submissions/1b7426aa-b153-4a60-be89-57016de17b0c

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
    (S : Finset V) (h : V → ℝ) :
    (∑ v, centeredVertexIndicator S v * h v) =
      Fintype.card V * (∑ v ∈ S, h v) -
        S.card * ∑ v, h v := by
  classical
  simp_rw [centeredVertexIndicator, sub_mul]
  rw [Finset.sum_sub_distrib]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  simp_rw [vertexIndicator, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite, Finset.filter_mem_eq_inter,
    Finset.filter_notMem_eq_sdiff]
  simp
end QEC.Coding.SmallSetExpansion
