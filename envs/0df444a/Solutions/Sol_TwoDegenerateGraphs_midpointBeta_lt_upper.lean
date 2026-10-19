-- Prove2me | solution 1 for TwoDegenerateGraphs.midpointBeta_lt_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/9c4a5bb7-1df4-45ac-b86b-22e53c626bdb

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (hwindow : entropyLowerEndpoint < entropyUpperEndpoint) :
    midpointBeta < entropyUpperEndpoint := by
  unfold midpointBeta
  linarith
end TwoDegenerateGraphs
