-- Prove2me | solution 1 for WeightedRootIntegralIdentity.bankBoundaryLimitPassage
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-20T11:24:02.531865+00:00
-- url     : https://prove2.me/submissions/5349ad2a-fc88-422c-a971-79e8ae01c1c9

import Mathlib
open Filter Topology

theorem solution
    (U L : ℝ → ℂ) (A B : ℂ)
    (hU : Tendsto U (𝓝[>] (0 : ℝ)) (𝓝 A))
    (hL : Tendsto L (𝓝[>] (0 : ℝ)) (𝓝 B)) :
    Tendsto (fun ε : ℝ => U ε + L ε) (𝓝[>] (0 : ℝ)) (𝓝 (A + B)) := by
  exact hU.add hL
