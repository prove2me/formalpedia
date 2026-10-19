-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingExpectedRetainedVertexCount_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:07.571959+00:00
-- url     : https://prove2.me/submissions/bb1b0a2d-9579-4d62-a2e9-ca1bde90c5cf

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingExpectedRetainedVertexCount_eq

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension : ℕ) :
    0 < hammingExpectedRetainedVertexCount dimension := by
  rw [hammingExpectedRetainedVertexCount_eq]
  have hprobability := hammingRetentionProbability_pos dimension
  positivity
end TwoDegenerateGraphs
