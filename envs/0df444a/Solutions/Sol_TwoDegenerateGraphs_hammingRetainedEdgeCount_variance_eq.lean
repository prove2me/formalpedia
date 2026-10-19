-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingRetainedEdgeCount_variance_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/0173170c-ca5e-4186-a504-4039c7e80836

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionMeasure_isProbability
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionMeasure_memLp_two
import Theorems.Thm_TwoDegenerateGraphs_hammingRetainedEdgeCount_integral_eq
import Theorems.Thm_TwoDegenerateGraphs_hammingRetainedEdgeCount_sq_integral_eq

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension radius : ℕ) :
    ProbabilityTheory.variance
        (hammingRetainedEdgeCount dimension radius)
        (hammingRetentionMeasure dimension) =
      hammingExpectedRetainedEdgeSquare dimension radius -
        hammingExpectedRetainedEdgeCount dimension radius ^ 2 := by
  letI : MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) :=
    hammingRetentionMeasure_isProbability dimension
  rw [ProbabilityTheory.variance_eq_sub
    (hammingRetentionMeasure_memLp_two dimension
      (hammingRetainedEdgeCount dimension radius))]
  change
    (∫ retained,
      hammingRetainedEdgeCount dimension radius retained ^ 2
        ∂hammingRetentionMeasure dimension) -
      (∫ retained,
        hammingRetainedEdgeCount dimension radius retained
          ∂hammingRetentionMeasure dimension) ^ 2 =
      hammingExpectedRetainedEdgeSquare dimension radius -
        hammingExpectedRetainedEdgeCount dimension radius ^ 2
  rw [hammingRetainedEdgeCount_sq_integral_eq,
    hammingRetainedEdgeCount_integral_eq]
end TwoDegenerateGraphs
