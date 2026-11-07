-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.weightedNeighborSum_centeredVertexIndicator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:44:02.236639+00:00
-- url     : https://prove2.me/submissions/16ba9b3b-a5eb-4149-b653-2e762cc7ac43

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
    (T : Finset V) (v : V) :
    weightedNeighborSum M (centeredVertexIndicator T) v =
      Fintype.card V * (∑ u ∈ T, (M v u : ℝ)) -
        degree * T.card := by
  classical
  have hDegree : (∑ u, (M v u : ℝ)) = degree := by
    exact_mod_cast hRegular v
  unfold weightedNeighborSum centeredVertexIndicator
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  · calc
      (∑ u, (M v u : ℝ) *
          ((Fintype.card V : ℝ) * vertexIndicator T u)) =
          (Fintype.card V : ℝ) *
            ∑ u, (M v u : ℝ) * vertexIndicator T u := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _hu
        ring
      _ = (Fintype.card V : ℝ) * ∑ u ∈ T, (M v u : ℝ) := by
        congr 1
        simp [vertexIndicator]
  · calc
      (∑ u, (M v u : ℝ) * (T.card : ℝ)) =
          (∑ u, (M v u : ℝ)) * T.card := by rw [Finset.sum_mul]
      _ = degree * T.card := by rw [hDegree]
end QEC.Coding.SmallSetExpansion
