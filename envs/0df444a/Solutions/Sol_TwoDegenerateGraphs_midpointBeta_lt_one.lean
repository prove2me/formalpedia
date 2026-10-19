-- Prove2me | solution 1 for TwoDegenerateGraphs.midpointBeta_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/11c08b8a-e4f8-4456-abe5-376c9b5f68b6

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_midpointBeta_lt_upper_unconditional
import Theorems.Thm_TwoDegenerateGraphs_entropyUpperEndpoint_lt_one

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution : midpointBeta < 1 :=
  midpointBeta_lt_upper_unconditional.trans entropyUpperEndpoint_lt_one
end TwoDegenerateGraphs
