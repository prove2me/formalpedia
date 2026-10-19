-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingRetainedVertexCount_variance_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/889719d4-f362-4ad7-8a0c-481c3ec66f1e

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingExpectedRetainedVertexVariance_le_mean
import Theorems.Thm_TwoDegenerateGraphs_hammingRetainedVertexCount_variance_eq

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension : ℕ) :
    ProbabilityTheory.variance
        (hammingRetainedVertexCount dimension)
        (hammingRetentionMeasure dimension) ≤
      hammingExpectedRetainedVertexCount dimension := by
  rw [hammingRetainedVertexCount_variance_eq]
  exact hammingExpectedRetainedVertexVariance_le_mean dimension
end TwoDegenerateGraphs
