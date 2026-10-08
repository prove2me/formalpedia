-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weightedRootUpperLowerLimitOrientedJump
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-20T06:20:32.588985+00:00
-- url     : https://prove2.me/submissions/2ed5a7d6-9a16-49ae-a14a-6357d4340480

import Mathlib
open Filter Topology

theorem solution
    (U L : ℕ → ℂ) (A : ℂ)
    (hU : Tendsto U atTop (𝓝 A))
    (hL : Tendsto L atTop (𝓝 (-starRingEnd ℂ A))) :
    Tendsto (fun m : ℕ => U m + L m) atTop
      (𝓝 (A - starRingEnd ℂ A)) := by
  simpa [sub_eq_add_neg] using hU.add hL
