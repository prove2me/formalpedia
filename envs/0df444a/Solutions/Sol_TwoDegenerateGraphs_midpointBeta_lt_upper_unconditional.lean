-- Prove2me | solution 1 for TwoDegenerateGraphs.midpointBeta_lt_upper_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/77d2dff6-a61e-4e3d-b0c7-990a5f016263

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_midpointBeta_lt_upper

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution :
    midpointBeta < entropyUpperEndpoint :=
  midpointBeta_lt_upper entropyWindow_pos
end TwoDegenerateGraphs
