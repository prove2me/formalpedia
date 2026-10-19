-- Prove2me | solution 1 for TwoDegenerateGraphs.sqrt_one_add_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/311d00b0-0730-441a-a04a-97c2b3922590

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (1 + x) ≤ 1 + x / 2 := by
  have hroot := Real.sqrt_nonneg (1 + x)
  have hsquare := Real.sq_sqrt (show 0 ≤ 1 + x by linarith)
  nlinarith [sq_nonneg x]
end TwoDegenerateGraphs
