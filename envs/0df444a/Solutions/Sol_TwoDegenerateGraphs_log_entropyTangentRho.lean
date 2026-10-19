-- Prove2me | solution 1 for TwoDegenerateGraphs.log_entropyTangentRho
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/47a69da3-e92d-4dd8-922d-681ffee2ad0e

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution :
    Real.log entropyTangentRho =
      (Real.log 2 - Real.log 3) / 2 := by
  unfold entropyTangentRho
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_sqrt (by positivity), Real.log_sqrt (by positivity)]
  ring
end TwoDegenerateGraphs
