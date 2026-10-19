-- Prove2me | solution 1 for TwoDegenerateGraphs.pairGraphCopyLayerPotential_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/0da9e24a-6fe5-4dd8-8c02-c0e0e238e5c4

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_binaryEntropy_nonneg
import Theorems.Thm_TwoDegenerateGraphs_binaryEntropy_le_one

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution
    {baseSize depth dimension radius : ℕ}
    (hbase : 4 ≤ baseSize)
    (hdimension : 0 < dimension)
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin (depth + 1)) :
    0 ≤ pairGraphCopyLayerPotential retained copy layer ∧
      pairGraphCopyLayerPotential retained copy layer ≤ 1 := by
  classical
  have hlayer :
      0 < Fintype.card (PairLayer baseSize layer.val) := by
    have hcard := pairLayer_card_ge_base
      baseSize layer.val hbase
    omega
  have hlayer_real :
      0 < (Fintype.card (PairLayer baseSize layer.val) : ℝ) := by
    exact_mod_cast hlayer
  have hdimension_real : 0 < (dimension : ℝ) := by
    exact_mod_cast hdimension
  have hterm (coordinate : Fin dimension) :
      0 ≤
        binaryEntropy
          (((booleanWordOnes
            (fun vertex : PairLayer baseSize layer.val =>
              (copy
                (pairLayerEmbedding baseSize depth layer.val layer.isLt
                  vertex)).val.2 coordinate)).card : ℝ) /
              (Fintype.card (PairLayer baseSize layer.val) : ℝ)) ∧
      binaryEntropy
          (((booleanWordOnes
            (fun vertex : PairLayer baseSize layer.val =>
              (copy
                (pairLayerEmbedding baseSize depth layer.val layer.isLt
                  vertex)).val.2 coordinate)).card : ℝ) /
              (Fintype.card (PairLayer baseSize layer.val) : ℝ)) ≤ 1 := by
    have hcount :
        (booleanWordOnes
          (fun vertex : PairLayer baseSize layer.val =>
            (copy
              (pairLayerEmbedding baseSize depth layer.val layer.isLt
                vertex)).val.2 coordinate)).card ≤
          Fintype.card (PairLayer baseSize layer.val) := by
      unfold booleanWordOnes
      simpa using
        (Finset.card_filter_le
          (Finset.univ : Finset (PairLayer baseSize layer.val))
          (fun vertex =>
            (copy
              (pairLayerEmbedding baseSize depth layer.val layer.isLt
                vertex)).val.2 coordinate = true))
    have hzero :
        0 ≤
          ((booleanWordOnes
            (fun vertex : PairLayer baseSize layer.val =>
              (copy
                (pairLayerEmbedding baseSize depth layer.val layer.isLt
                  vertex)).val.2 coordinate)).card : ℝ) /
            (Fintype.card (PairLayer baseSize layer.val) : ℝ) := by
      positivity
    have hone :
        ((booleanWordOnes
          (fun vertex : PairLayer baseSize layer.val =>
            (copy
              (pairLayerEmbedding baseSize depth layer.val layer.isLt
                vertex)).val.2 coordinate)).card : ℝ) /
            (Fintype.card (PairLayer baseSize layer.val) : ℝ) ≤ 1 := by
      apply (div_le_one hlayer_real).mpr
      exact_mod_cast hcount
    exact ⟨binaryEntropy_nonneg hzero hone,
      binaryEntropy_le_one _⟩
  unfold pairGraphCopyLayerPotential
  constructor
  · apply div_nonneg
    · exact Finset.sum_nonneg
        (fun coordinate _ => (hterm coordinate).1)
    · exact hdimension_real.le
  · apply (div_le_one hdimension_real).mpr
    calc
      (∑ coordinate : Fin dimension,
        binaryEntropy
          (((booleanWordOnes
            (fun vertex : PairLayer baseSize layer.val =>
              (copy
                (pairLayerEmbedding baseSize depth layer.val layer.isLt
                  vertex)).val.2 coordinate)).card : ℝ) /
              (Fintype.card (PairLayer baseSize layer.val) : ℝ))) ≤
        ∑ _coordinate : Fin dimension, (1 : ℝ) := by
          exact Finset.sum_le_sum
            (fun coordinate _ => (hterm coordinate).2)
      _ = (dimension : ℝ) := by
        simp
end TwoDegenerateGraphs
