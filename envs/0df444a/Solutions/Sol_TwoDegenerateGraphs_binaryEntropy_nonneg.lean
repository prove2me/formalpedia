-- Prove2me | solution 1 for TwoDegenerateGraphs.binaryEntropy_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/03823f15-63ff-46d2-b312-35486d4cca6e

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution {x : ℝ} (hzero : 0 ≤ x)
    (hone : x ≤ 1) : 0 ≤ binaryEntropy x := by
  exact div_nonneg (Real.binEntropy_nonneg hzero hone) log_two_pos.le
end TwoDegenerateGraphs
