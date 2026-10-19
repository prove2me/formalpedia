-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingRetainedVertexCount_deviation_probability_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/12cce4d1-3fc2-4e77-8309-fa7caa9f9f98

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionMeasure_real_deviation_le
import Theorems.Thm_TwoDegenerateGraphs_hammingRetainedVertexCount_integral_eq
import Theorems.Thm_TwoDegenerateGraphs_hammingRetainedVertexCount_variance_le

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension : ℕ) (threshold : ℝ)
    (hthreshold : 0 < threshold) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        threshold ≤
          |hammingRetainedVertexCount dimension retained -
            hammingExpectedRetainedVertexCount dimension|} ≤
      hammingExpectedRetainedVertexCount dimension / threshold ^ 2 := by
  have hchebyshev := hammingRetentionMeasure_real_deviation_le
    dimension (hammingRetainedVertexCount dimension)
    threshold hthreshold
  rw [hammingRetainedVertexCount_integral_eq] at hchebyshev
  calc
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        threshold ≤
          |hammingRetainedVertexCount dimension retained -
            hammingExpectedRetainedVertexCount dimension|} ≤
      ProbabilityTheory.variance
          (hammingRetainedVertexCount dimension)
          (hammingRetentionMeasure dimension) /
        threshold ^ 2 := hchebyshev
    _ ≤ hammingExpectedRetainedVertexCount dimension /
        threshold ^ 2 := by
      gcongr
      exact hammingRetainedVertexCount_variance_le dimension
end TwoDegenerateGraphs
