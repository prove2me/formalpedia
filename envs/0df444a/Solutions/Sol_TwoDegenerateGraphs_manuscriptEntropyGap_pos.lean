-- Prove2me | solution 1 for TwoDegenerateGraphs.manuscriptEntropyGap_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/beb9a269-c2cf-4908-a500-e8e18032c1a8

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution : 0 < manuscriptEntropyGap := by
  unfold manuscriptEntropyGap
  positivity [certifiedWindowWidth_pos, log_two_pos]
end TwoDegenerateGraphs
