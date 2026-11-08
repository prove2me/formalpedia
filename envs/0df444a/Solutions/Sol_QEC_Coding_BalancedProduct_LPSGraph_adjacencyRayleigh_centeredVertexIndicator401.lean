-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSGraph.adjacencyRayleigh_centeredVertexIndicator401
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:24:03.284971+00:00
-- url     : https://prove2.me/submissions/2cba25a7-e9ca-4326-b891-6313607bedee

import Definitions.Def_QEC_Coding_BalancedProduct_LPSGenerators
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Real.Basic
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGraph
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSGraph_card_lpsNeighbors401
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSGraph_sum_vertexIndicator401
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSGraph_sum_neighbor_vertexIndicator401
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSGraph_adjacencyRayleigh_vertexIndicator401
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSGraph_sum_neighbor_vertexIndicator401_over_vertices

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
    adjacencyRayleigh401 q hq (centeredVertexIndicator401 q S) =
      (Fintype.card (PGL(2, ZMod q)) : ℝ) ^ 2 *
          insideAdjacencyCount401 q hq S -
        402 * Fintype.card (PGL(2, ZMod q)) * S.card ^ 2 := by
  classical
  let n : ℝ := Fintype.card (PGL(2, ZMod q))
  let m : ℝ := S.card
  have hinner (v : PGL(2, ZMod q)) :
      (∑ w ∈ lpsNeighbors401 q hq v,
          centeredVertexIndicator401 q S w) =
        n * (lpsNeighborsIn401 q hq S v).card - 402 * m := by
    unfold centeredVertexIndicator401
    rw [Finset.sum_sub_distrib]
    simp_rw [← Finset.mul_sum]
    rw [sum_neighbor_vertexIndicator401]
    rw [Finset.sum_const, card_lpsNeighbors401 q hq40 hq]
    simp only [nsmul_eq_mul]
    dsimp [n, m]
  have hinside :
      (∑ v, vertexIndicator401 q S v *
          ((lpsNeighborsIn401 q hq S v).card : ℝ)) =
        insideAdjacencyCount401 q hq S := by
    rw [← adjacencyRayleigh_vertexIndicator401 q hq S]
    unfold adjacencyRayleigh401
    simp_rw [sum_neighbor_vertexIndicator401]
  have hcount :
      (∑ v, ((lpsNeighborsIn401 q hq S v).card : ℝ)) = 402 * m := by
    have h := sum_neighbor_vertexIndicator401_over_vertices q hq40 hq S
    simp_rw [sum_neighbor_vertexIndicator401] at h
    simpa only [m] using h
  have hA :
      (∑ v, n * vertexIndicator401 q S v *
          (n * (lpsNeighborsIn401 q hq S v).card)) =
        n ^ 2 * insideAdjacencyCount401 q hq S := by
    calc
      _ = n ^ 2 * ∑ v, vertexIndicator401 q S v *
          ((lpsNeighborsIn401 q hq S v).card : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _hv
        ring
      _ = n ^ 2 * insideAdjacencyCount401 q hq S := by rw [hinside]
  have hB :
      (∑ v, n * vertexIndicator401 q S v * (402 * m)) =
        402 * n * m ^ 2 := by
    calc
      _ = (402 * n * m) * ∑ v, vertexIndicator401 q S v := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _hv
        ring
      _ = 402 * n * m ^ 2 := by
        rw [sum_vertexIndicator401]
        change 402 * n * m * m = 402 * n * m ^ 2
        ring
  have hC :
      (∑ v, m * (n * (lpsNeighborsIn401 q hq S v).card)) =
        402 * n * m ^ 2 := by
    calc
      _ = (m * n) * ∑ v,
          ((lpsNeighborsIn401 q hq S v).card : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _hv
        ring
      _ = 402 * n * m ^ 2 := by rw [hcount]; ring
  have hD :
      (∑ _v : PGL(2, ZMod q), m * (402 * m)) = 402 * n * m ^ 2 := by
    rw [Finset.sum_const]
    simp only [nsmul_eq_mul]
    dsimp [n]
    ring
  rw [adjacencyRayleigh401]
  simp_rw [hinner]
  unfold centeredVertexIndicator401
  change (∑ v,
      (n * vertexIndicator401 q S v - m) *
        (n * (lpsNeighborsIn401 q hq S v).card - 402 * m)) =
    n ^ 2 * insideAdjacencyCount401 q hq S - 402 * n * m ^ 2
  simp_rw [sub_mul, mul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib]
  rw [hA, hB, hC, hD]
  ring
end QEC.Coding.BalancedProduct.LPSGraph
