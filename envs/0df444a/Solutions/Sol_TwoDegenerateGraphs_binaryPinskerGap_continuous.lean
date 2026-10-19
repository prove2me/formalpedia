-- Prove2me | solution 1 for TwoDegenerateGraphs.binaryPinskerGap_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/4749d85c-d8d3-424a-a4ca-609c9d76eaa5

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution : Continuous binaryPinskerGap := by
  unfold binaryPinskerGap
  fun_prop
end TwoDegenerateGraphs
