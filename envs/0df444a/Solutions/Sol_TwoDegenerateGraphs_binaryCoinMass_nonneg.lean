-- Prove2me | solution 1 for TwoDegenerateGraphs.binaryCoinMass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/542493a7-b46d-41e8-bb2c-fe17380f342e

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution {q : ℝ}
    (hqzero : 0 ≤ q) (hqone : q ≤ 1) (outcome : Bool) :
    0 ≤ binaryCoinMass q outcome := by
  cases outcome <;> simp [binaryCoinMass] <;> linarith
end TwoDegenerateGraphs
