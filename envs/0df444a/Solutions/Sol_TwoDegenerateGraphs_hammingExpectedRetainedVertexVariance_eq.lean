-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingExpectedRetainedVertexVariance_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:07.571959+00:00
-- url     : https://prove2.me/submissions/e5deb2af-98f3-4313-9088-35e760dcd72b

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingExpectedRetainedVertexCount_eq
import Theorems.Thm_TwoDegenerateGraphs_hammingExpectedRetainedVertexSquare_eq

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension : ℕ) :
    hammingExpectedRetainedVertexSquare dimension -
        hammingExpectedRetainedVertexCount dimension ^ 2 =
      (((2 * 2 ^ dimension : ℕ) : ℝ)) *
        hammingRetentionProbability dimension *
        (1 - hammingRetentionProbability dimension) := by
  rw [hammingExpectedRetainedVertexSquare_eq,
    hammingExpectedRetainedVertexCount_eq]
  push_cast
  ring
end TwoDegenerateGraphs
