-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSGraph.adjacencyRayleigh_vertexIndicator401
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:04:17.6622+00:00
-- url     : https://prove2.me/submissions/451a78a5-fc4f-436a-a0cf-34ea33abf973

import Definitions.Def_QEC_Coding_BalancedProduct_LPSGenerators
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Real.Basic
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGraph
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSGraph_vertexIndicator401_of_mem
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSGraph_vertexIndicator401_of_not_mem
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSGraph_sum_neighbor_vertexIndicator401

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSGraph
open Matrix
open LPSArithmetic LPSGenerators
namespace QEC.Coding.BalancedProduct.LPSGraph
theorem _root_.solution
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (S : Finset (PGL(2, ZMod q))) :
    adjacencyRayleigh401 q hq (vertexIndicator401 q S) =
      insideAdjacencyCount401 q hq S := by
  classical
  rw [adjacencyRayleigh401, insideAdjacencyCount401]
  simp_rw [sum_neighbor_vertexIndicator401]
  push_cast
  calc
    (∑ v,
        vertexIndicator401 q S v *
          ((lpsNeighborsIn401 q hq S v).card : ℝ)) =
        ∑ v ∈ S,
          vertexIndicator401 q S v *
            ((lpsNeighborsIn401 q hq S v).card : ℝ) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro v _hvUniv hvS
      rw [vertexIndicator401_of_not_mem q S hvS, zero_mul]
    _ = ∑ v ∈ S, ((lpsNeighborsIn401 q hq S v).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro v hvS
      rw [vertexIndicator401_of_mem q S hvS, one_mul]
end QEC.Coding.BalancedProduct.LPSGraph
