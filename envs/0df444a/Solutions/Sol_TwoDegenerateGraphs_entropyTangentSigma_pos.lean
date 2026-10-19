-- Prove2me | solution 1 for TwoDegenerateGraphs.entropyTangentSigma_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/5c01d397-de19-471f-ad98-d15d7c2fa26e

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution : 0 < entropyTangentSigma := by
  unfold entropyTangentSigma
  positivity
end TwoDegenerateGraphs
