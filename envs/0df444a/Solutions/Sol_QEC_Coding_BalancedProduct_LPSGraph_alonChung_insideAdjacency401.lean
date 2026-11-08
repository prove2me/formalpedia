-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSGraph.alonChung_insideAdjacency401
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:24:54.520537+00:00
-- url     : https://prove2.me/submissions/28b10f64-6e09-4709-9d46-6ef3de0631de

import Definitions.Def_QEC_Coding_BalancedProduct_LPSGenerators
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Real.Basic
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGraph
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSGraph_sum_centeredVertexIndicator401
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSGraph_sum_sq_centeredVertexIndicator401
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSGraph_adjacencyRayleigh_centeredVertexIndicator401

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSGraph
open Matrix
open LPSArithmetic LPSGenerators
namespace QEC.Coding.BalancedProduct.LPSGraph
theorem _root_.solution
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (hLPS : LPS401RayleighBound q hq)
    (S : Finset (PGL(2, ZMod q))) :
    10 * (Fintype.card (PGL(2, ZMod q)) : ℝ) *
        (insideAdjacencyCount401 q hq S : ℝ) ≤
      401 * (S.card : ℝ) *
          ((Fintype.card (PGL(2, ZMod q)) : ℝ) - S.card) +
        4020 * (S.card : ℝ) ^ 2 := by
  let n : ℝ := Fintype.card (PGL(2, ZMod q))
  let m : ℝ := S.card
  let d : ℝ := insideAdjacencyCount401 q hq S
  have hspectral := hLPS.2 (centeredVertexIndicator401 q S)
    (sum_centeredVertexIndicator401 q S)
  rw [adjacencyRayleigh_centeredVertexIndicator401 q hq40 hq S,
    sum_sq_centeredVertexIndicator401 q S] at hspectral
  have hn : 0 < n := by
    dsimp [n]
    positivity
  change 10 * n * d ≤ 401 * m * (n - m) + 4020 * m ^ 2
  change
    10 * (n ^ 2 * d - 402 * n * m ^ 2) ≤
      401 * (n * m * (n - m)) at hspectral
  nlinarith
end QEC.Coding.BalancedProduct.LPSGraph
