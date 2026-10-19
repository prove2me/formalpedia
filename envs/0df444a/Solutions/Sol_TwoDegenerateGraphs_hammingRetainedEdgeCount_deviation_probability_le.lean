-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingRetainedEdgeCount_deviation_probability_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/d89fab28-c1b1-43ea-ba33-75d2869ccd56

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionMeasure_real_deviation_le
import Theorems.Thm_TwoDegenerateGraphs_hammingRetainedEdgeCount_integral_eq
import Theorems.Thm_TwoDegenerateGraphs_hammingRetainedEdgeCount_variance_le

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension radius : ℕ) (threshold : ℝ)
    (hthreshold : 0 < threshold) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        threshold ≤
          |hammingRetainedEdgeCount dimension radius retained -
            hammingExpectedRetainedEdgeCount dimension radius|} ≤
      (hammingExpectedRetainedEdgeCount dimension radius +
        2 * hammingRetentionProbability dimension ^ 3 *
          ((2 ^ dimension : ℕ) : ℝ) *
          ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) ^ 2) /
        threshold ^ 2 := by
  have hchebyshev := hammingRetentionMeasure_real_deviation_le
    dimension (hammingRetainedEdgeCount dimension radius)
    threshold hthreshold
  rw [hammingRetainedEdgeCount_integral_eq] at hchebyshev
  calc
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        threshold ≤
          |hammingRetainedEdgeCount dimension radius retained -
            hammingExpectedRetainedEdgeCount dimension radius|} ≤
      ProbabilityTheory.variance
          (hammingRetainedEdgeCount dimension radius)
          (hammingRetentionMeasure dimension) /
        threshold ^ 2 := hchebyshev
    _ ≤
      (hammingExpectedRetainedEdgeCount dimension radius +
        2 * hammingRetentionProbability dimension ^ 3 *
          ((2 ^ dimension : ℕ) : ℝ) *
          ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) ^ 2) /
        threshold ^ 2 := by
      gcongr
      exact hammingRetainedEdgeCount_variance_le dimension radius
end TwoDegenerateGraphs
