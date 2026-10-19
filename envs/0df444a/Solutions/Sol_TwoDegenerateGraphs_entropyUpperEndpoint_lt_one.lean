-- Prove2me | solution 1 for TwoDegenerateGraphs.entropyUpperEndpoint_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/1aa62737-5277-4207-bf1a-763a5fd2ac19

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_binaryEntropy_tau_lt_one

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution : entropyUpperEndpoint < 1 := by
  unfold entropyUpperEndpoint
  nlinarith [binaryEntropy_tau_lt_one]
end TwoDegenerateGraphs
