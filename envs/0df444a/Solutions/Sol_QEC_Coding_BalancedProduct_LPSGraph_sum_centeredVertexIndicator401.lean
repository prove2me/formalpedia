-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSGraph.sum_centeredVertexIndicator401
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:03:53.33911+00:00
-- url     : https://prove2.me/submissions/1157e7a7-4fe9-407e-9c9e-724ca81e9391

import Definitions.Def_QEC_Coding_BalancedProduct_LPSGenerators
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Real.Basic
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGraph
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
    ∑ v, centeredVertexIndicator401 q S v = 0 := by
  classical
  unfold centeredVertexIndicator401
  rw [Finset.sum_sub_distrib]
  simp_rw [← Finset.mul_sum]
  rw [sum_vertexIndicator401]
  simp
end QEC.Coding.BalancedProduct.LPSGraph
