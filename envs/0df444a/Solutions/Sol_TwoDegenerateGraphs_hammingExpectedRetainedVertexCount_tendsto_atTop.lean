-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingExpectedRetainedVertexCount_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:07.571959+00:00
-- url     : https://prove2.me/submissions/404ac681-ffc3-4a06-8b56-680159dc6ebe

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionProbability_mul_wordCount_tendsto_atTop
import Theorems.Thm_TwoDegenerateGraphs_hammingExpectedRetainedVertexCount_eq

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution :
    Tendsto hammingExpectedRetainedVertexCount atTop atTop := by
  have hgrowth :=
    hammingRetentionProbability_mul_wordCount_tendsto_atTop.const_mul_atTop
      (by norm_num : (0 : ℝ) < 2)
  apply hgrowth.congr'
  filter_upwards [] with dimension
  rw [hammingExpectedRetainedVertexCount_eq]
  ring
end TwoDegenerateGraphs
