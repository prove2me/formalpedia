-- Prove2me | solution 1 for TwoDegenerateGraphs.binaryEntropy_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/f5891a21-06b8-4e90-9f6f-9a0d61c35f84

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution (x : ℝ) : binaryEntropy x ≤ 1 := by
  unfold binaryEntropy
  apply (div_le_iff₀ log_two_pos).2
  simpa using (Real.binEntropy_le_log_two (p := x))
end TwoDegenerateGraphs
