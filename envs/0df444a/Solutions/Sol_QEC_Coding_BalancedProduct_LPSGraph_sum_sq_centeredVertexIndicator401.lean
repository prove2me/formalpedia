-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSGraph.sum_sq_centeredVertexIndicator401
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:04:19.196625+00:00
-- url     : https://prove2.me/submissions/249ad1d1-d878-4926-88e8-39cafd0f0746

import Definitions.Def_QEC_Coding_BalancedProduct_LPSGenerators
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Real.Basic
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGraph
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSGraph_vertexIndicator401_of_mem
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSGraph_vertexIndicator401_of_not_mem
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSGraph_sum_vertexIndicator401

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSGraph
open Matrix
open LPSArithmetic LPSGenerators
namespace QEC.Coding.BalancedProduct.LPSGraph
theorem _root_.solution
    (q : ℕ) [Fact q.Prime]
    (S : Finset (PGL(2, ZMod q))) :
    ∑ v, (centeredVertexIndicator401 q S v) ^ 2 =
      (Fintype.card (PGL(2, ZMod q)) : ℝ) * S.card *
        (Fintype.card (PGL(2, ZMod q)) - S.card) := by
  classical
  let n : ℝ := Fintype.card (PGL(2, ZMod q))
  let m : ℝ := S.card
  have hsq (v : PGL(2, ZMod q)) :
      (vertexIndicator401 q S v) ^ 2 = vertexIndicator401 q S v := by
    by_cases hv : v ∈ S
    · rw [vertexIndicator401_of_mem q S hv]
      norm_num
    · rw [vertexIndicator401_of_not_mem q S hv]
      norm_num
  change (∑ v, (n * vertexIndicator401 q S v - m) ^ 2) =
    n * m * (n - m)
  have hcross :
      (∑ v, 2 * (n * vertexIndicator401 q S v) * m) = 2 * n * m * m := by
    calc
      (∑ v, 2 * (n * vertexIndicator401 q S v) * m) =
          (2 * n * m) * ∑ v, vertexIndicator401 q S v := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _hv
        ring
      _ = 2 * n * m * m := by
        rw [sum_vertexIndicator401]
  simp_rw [sub_sq, mul_pow, hsq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [← Finset.mul_sum]
  rw [sum_vertexIndicator401]
  rw [hcross]
  simp [n, m]
  ring
end QEC.Coding.BalancedProduct.LPSGraph
