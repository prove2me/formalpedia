-- Prove2me | solution 1 for TwoDegenerateGraphs.badPairLayersRetentionEvent_real_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/922d2dac-0fda-4364-9619-d13d5228cc64

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_badPairLayerRetentionEvent_real_lt_exp_neg

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    {depth dimension : ℕ}
    (layerSizes : Fin depth → ℕ)
    (hdimension : 0 < dimension)
    (hparents : ∀ layer, 4 ≤ layerSizes layer)
    (hbase : ∀ layer,
      (layerSizes layer : ℝ) +
        3 * logTwo
          (((layerSizes layer).choose 2 + 1 : ℕ) : ℝ) -
          entropySlack * ((layerSizes layer).choose 2 : ℝ) < -1) :
    (hammingRetentionMeasure dimension).real
        (badPairLayersRetentionEvent layerSizes dimension) ≤
      (((2 * depth : ℕ) : ℝ)) *
        Real.exp (-(dimension : ℝ) * Real.log 2) := by
  classical
  let bound : ℝ := Real.exp (-(dimension : ℝ) * Real.log 2)
  calc
    (hammingRetentionMeasure dimension).real
        (badPairLayersRetentionEvent layerSizes dimension) =
      (hammingRetentionMeasure dimension).real
        (⋃ side : Bool, ⋃ layer : Fin depth,
          badPairLayerRetentionEvent (layerSizes layer) dimension side
            (midpointBeta - entropySlack)) := by
        rfl
    _ ≤ ∑ side : Bool,
        (hammingRetentionMeasure dimension).real
          (⋃ layer : Fin depth,
            badPairLayerRetentionEvent (layerSizes layer) dimension side
              (midpointBeta - entropySlack)) :=
        MeasureTheory.measureReal_iUnion_fintype_le
          (fun side =>
            ⋃ layer : Fin depth,
              badPairLayerRetentionEvent (layerSizes layer) dimension side
                (midpointBeta - entropySlack))
    _ ≤ ∑ side : Bool, ∑ layer : Fin depth,
          (hammingRetentionMeasure dimension).real
            (badPairLayerRetentionEvent
              (layerSizes layer) dimension side
                (midpointBeta - entropySlack)) := by
        apply Finset.sum_le_sum
        intro side _
        exact MeasureTheory.measureReal_iUnion_fintype_le
          (fun layer =>
            badPairLayerRetentionEvent
              (layerSizes layer) dimension side
                (midpointBeta - entropySlack))
    _ ≤ ∑ _side : Bool, ∑ _layer : Fin depth, bound := by
        apply Finset.sum_le_sum
        intro side _
        apply Finset.sum_le_sum
        intro layer _
        exact (badPairLayerRetentionEvent_real_lt_exp_neg
          (hparents layer) hdimension (hbase layer) side).le
    _ = (((2 * depth : ℕ) : ℝ)) *
          Real.exp (-(dimension : ℝ) * Real.log 2) := by
        simp [bound, nsmul_eq_mul]
        ring
end TwoDegenerateGraphs
