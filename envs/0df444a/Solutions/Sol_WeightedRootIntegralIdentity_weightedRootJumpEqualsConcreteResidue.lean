-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weightedRootJumpEqualsConcreteResidue
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-20T06:25:52.825983+00:00
-- url     : https://prove2.me/submissions/74c1f3a6-a1a9-4b14-931f-b1901203841c

import Mathlib
open Filter Topology

theorem solution
    (U L : ℕ → ℂ) (A R : ℂ)
    (hU : Tendsto U atTop (𝓝 A))
    (hL : Tendsto L atTop (𝓝 (-starRingEnd ℂ A)))
    (hres : Tendsto (fun m : ℕ => U m + L m) atTop (𝓝 R)) :
    A - starRingEnd ℂ A = R := by
  have hjump : Tendsto (fun m : ℕ => U m + L m) atTop
      (𝓝 (A - starRingEnd ℂ A)) := by
    simpa [sub_eq_add_neg] using hU.add hL
  exact tendsto_nhds_unique hjump hres
