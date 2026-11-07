-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.sum_sq_centeredVertexIndicator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:43:03.762759+00:00
-- url     : https://prove2.me/submissions/17b71365-47b4-49d1-a770-8e0c93e478cd

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Mathlib.Data.Nat.Log
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Theorems.Thm_QEC_Coding_SmallSetExpansion_sum_vertexIndicator

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
theorem _root_.solution [Fintype V] [DecidableEq V]
    (S : Finset V) :
    ∑ v, (centeredVertexIndicator S v) ^ 2 =
      (Fintype.card V : ℝ) * S.card *
        (Fintype.card V - S.card) := by
  classical
  let n : ℝ := Fintype.card V
  let s : ℝ := S.card
  have hsq (v : V) : (vertexIndicator S v) ^ 2 = vertexIndicator S v := by
    by_cases hv : v ∈ S <;> simp [vertexIndicator, hv]
  change (∑ v, (n * vertexIndicator S v - s) ^ 2) = n * s * (n - s)
  have hcross :
      (∑ v, 2 * (n * vertexIndicator S v) * s) = 2 * n * s * s := by
    calc
      (∑ v, 2 * (n * vertexIndicator S v) * s) =
          (2 * n * s) * ∑ v, vertexIndicator S v := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _hv
        ring
      _ = 2 * n * s * s := by rw [sum_vertexIndicator]
  simp_rw [sub_sq, mul_pow, hsq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [← Finset.mul_sum]
  rw [sum_vertexIndicator]
  rw [hcross]
  simp [n, s]
  ring
end QEC.Coding.SmallSetExpansion
