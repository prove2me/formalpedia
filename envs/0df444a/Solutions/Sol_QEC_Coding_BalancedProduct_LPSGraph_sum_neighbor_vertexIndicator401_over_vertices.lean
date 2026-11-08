-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSGraph.sum_neighbor_vertexIndicator401_over_vertices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:21:49.578585+00:00
-- url     : https://prove2.me/submissions/f18ee46c-9828-440c-8caa-11f602e2f0ce

import Definitions.Def_QEC_Coding_BalancedProduct_LPSGenerators
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Real.Basic
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGraph
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSGraph_sum_vertexIndicator401
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSGraph_sum_lpsNeighbors401_eq_sum_generators
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSGenerators_card_lpsGenerators401


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
    (S : Finset (PGL(2, ZMod q))) :
    ∑ v, ∑ w ∈ lpsNeighbors401 q hq v, vertexIndicator401 q S w =
      402 * S.card := by
  classical
  calc
    (∑ v, ∑ w ∈ lpsNeighbors401 q hq v,
        vertexIndicator401 q S w) =
        ∑ v, ∑ s ∈ lpsGenerators401 q hq,
          vertexIndicator401 q S (s * v) := by
      apply Finset.sum_congr rfl
      intro v _hv
      exact sum_lpsNeighbors401_eq_sum_generators q hq v
        (vertexIndicator401 q S)
    _ = ∑ s ∈ lpsGenerators401 q hq,
          ∑ v, vertexIndicator401 q S (s * v) := by
      rw [Finset.sum_comm]
    _ = ∑ s ∈ lpsGenerators401 q hq,
          ∑ v, vertexIndicator401 q S v := by
      apply Finset.sum_congr rfl
      intro s _hs
      exact Equiv.sum_comp (Equiv.mulLeft s) (vertexIndicator401 q S)
    _ = 402 * S.card := by
      rw [sum_vertexIndicator401]
      simp [card_lpsGenerators401 q hq40 hq]
end QEC.Coding.BalancedProduct.LPSGraph
