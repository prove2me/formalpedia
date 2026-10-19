-- Prove2me | solution 1 for TwoDegenerateGraphs.manuscriptSamplingFailureEvent_real_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/bad85420-56a5-40d8-8d17-3486e7b41da6

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingRetainedVertexCount_upper_tail_probability_le
import Theorems.Thm_TwoDegenerateGraphs_badPairLayersRetentionEvent_real_le
import Theorems.Thm_TwoDegenerateGraphs_hammingRetainedEdgeCount_lower_tail_probability_le

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
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
      (manuscriptSamplingFailureEvent layerSizes dimension) ≤
        manuscriptSamplingFailureBound depth dimension := by
  let vertexFailure : Set (Set (Bool × HammingWord dimension)) :=
    {retained : Set (Bool × HammingWord dimension) |
      3 * hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ) ≤
        hammingRetainedVertexCount dimension retained}
  let edgeFailure : Set (Set (Bool × HammingWord dimension)) :=
    {retained : Set (Bool × HammingWord dimension) |
      hammingRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension) retained <
        hammingExpectedRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension) / 2}
  change
    (hammingRetentionMeasure dimension).real
      ((badPairLayersRetentionEvent layerSizes dimension ∪
        vertexFailure) ∪ edgeFailure) ≤
        manuscriptSamplingFailureBound depth dimension
  calc
    (hammingRetentionMeasure dimension).real
      ((badPairLayersRetentionEvent layerSizes dimension ∪
        vertexFailure) ∪ edgeFailure) ≤
      ((hammingRetentionMeasure dimension).real
        (badPairLayersRetentionEvent layerSizes dimension) +
       (hammingRetentionMeasure dimension).real vertexFailure) +
        (hammingRetentionMeasure dimension).real edgeFailure := by
      calc
        (hammingRetentionMeasure dimension).real
          ((badPairLayersRetentionEvent layerSizes dimension ∪
            vertexFailure) ∪ edgeFailure) ≤
          (hammingRetentionMeasure dimension).real
            (badPairLayersRetentionEvent layerSizes dimension ∪
              vertexFailure) +
            (hammingRetentionMeasure dimension).real edgeFailure :=
              MeasureTheory.measureReal_union_le _ _
        _ ≤ ((hammingRetentionMeasure dimension).real
              (badPairLayersRetentionEvent layerSizes dimension) +
            (hammingRetentionMeasure dimension).real vertexFailure) +
            (hammingRetentionMeasure dimension).real edgeFailure := by
              gcongr
              exact MeasureTheory.measureReal_union_le _ _
    _ ≤ ((((2 * depth : ℕ) : ℝ)) *
          Real.exp (-(dimension : ℝ) * Real.log 2) +
        4 / hammingExpectedRetainedVertexCount dimension) +
        (4 / hammingExpectedRetainedEdgeCount dimension
            (manuscriptHammingRadius dimension) +
          8 / (hammingRetentionProbability dimension *
            ((2 ^ dimension : ℕ) : ℝ))) := by
      gcongr
      · exact badPairLayersRetentionEvent_real_le
          layerSizes hdimension hparents hbase
      · exact hammingRetainedVertexCount_upper_tail_probability_le dimension
      · exact hammingRetainedEdgeCount_lower_tail_probability_le
          dimension (manuscriptHammingRadius dimension)
    _ = manuscriptSamplingFailureBound depth dimension := by
      rfl
end TwoDegenerateGraphs
