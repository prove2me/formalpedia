-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingRetainedVertexCount_variance_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:07.571959+00:00
-- url     : https://prove2.me/submissions/ea65999a-1e02-480b-a02c-96f6e8a22ea0

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionMeasure_isProbability
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionMeasure_memLp_two
import Theorems.Thm_TwoDegenerateGraphs_hammingRetainedVertexCount_integral_eq
import Theorems.Thm_TwoDegenerateGraphs_hammingRetainedVertexCount_sq_integral_eq

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension : ℕ) :
    ProbabilityTheory.variance
        (hammingRetainedVertexCount dimension)
        (hammingRetentionMeasure dimension) =
      hammingExpectedRetainedVertexSquare dimension -
        hammingExpectedRetainedVertexCount dimension ^ 2 := by
  letI : MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) :=
    hammingRetentionMeasure_isProbability dimension
  rw [ProbabilityTheory.variance_eq_sub
    (hammingRetentionMeasure_memLp_two dimension
      (hammingRetainedVertexCount dimension))]
  change
    (∫ retained,
      hammingRetainedVertexCount dimension retained ^ 2
        ∂hammingRetentionMeasure dimension) -
      (∫ retained,
        hammingRetainedVertexCount dimension retained
          ∂hammingRetentionMeasure dimension) ^ 2 =
      hammingExpectedRetainedVertexSquare dimension -
        hammingExpectedRetainedVertexCount dimension ^ 2
  rw [hammingRetainedVertexCount_sq_integral_eq,
    hammingRetainedVertexCount_integral_eq]
end TwoDegenerateGraphs
