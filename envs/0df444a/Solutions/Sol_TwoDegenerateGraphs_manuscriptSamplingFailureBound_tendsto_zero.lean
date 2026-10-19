-- Prove2me | solution 1 for TwoDegenerateGraphs.manuscriptSamplingFailureBound_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/885713fa-4bfc-4a94-8c71-daecdae0bee4

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionProbability_mul_wordCount_inv_tendsto_zero
import Theorems.Thm_TwoDegenerateGraphs_hammingExpectedRetainedVertexCount_inv_tendsto_zero
import Theorems.Thm_TwoDegenerateGraphs_pairLayerExclusionProbability_tendsto_zero
import Theorems.Thm_TwoDegenerateGraphs_manuscriptExpectedRetainedEdgeCount_inv_tendsto_zero

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution
    (depth : ℕ) :
    Tendsto
      (manuscriptSamplingFailureBound depth)
      atTop (𝓝 0) := by
  have hexclusion := pairLayerExclusionProbability_tendsto_zero depth
  have hvertices :=
    hammingExpectedRetainedVertexCount_inv_tendsto_zero.const_mul 4
  have hedges :=
    manuscriptExpectedRetainedEdgeCount_inv_tendsto_zero.const_mul 4
  have hwords :=
    hammingRetentionProbability_mul_wordCount_inv_tendsto_zero.const_mul 8
  have htotal := (hexclusion.add hvertices).add (hedges.add hwords)
  have htotal_zero :
      Tendsto
        (fun dimension : ℕ =>
          (((2 * depth : ℕ) : ℝ)) *
              Real.exp (-(dimension : ℝ) * Real.log 2) +
            4 * (1 / hammingExpectedRetainedVertexCount dimension) +
            (4 * (1 / hammingExpectedRetainedEdgeCount dimension
                (manuscriptHammingRadius dimension)) +
              8 * (1 / (hammingRetentionProbability dimension *
                ((2 ^ dimension : ℕ) : ℝ)))))
        atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using htotal
  apply htotal_zero.congr'
  filter_upwards [] with dimension
  unfold manuscriptSamplingFailureBound
  push_cast
  simp only [div_eq_mul_inv]
  ring
end TwoDegenerateGraphs
