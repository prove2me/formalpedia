-- Prove2me | solution 1 for WeightedRootIntegralIdentity.finiteKeyholeLimitAssembly
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-20T11:17:41.900162+00:00
-- url     : https://prove2.me/submissions/c46051b5-f494-46ab-a1e5-0a08abcfd8c7

import Mathlib
import Theorems.Thm_WeightedRootIntegralIdentity_weightedRootJumpEqualsConcreteResidue
open Filter Topology

theorem solution
    (U L : ℕ → ℂ) (A ρ : ℂ)
    (hU : Tendsto U atTop (𝓝 A))
    (hL : Tendsto L atTop (𝓝 (-starRingEnd ℂ A)))
    (hres : Tendsto (fun m : ℕ => U m + L m) atTop (𝓝 ρ)) :
    A - starRingEnd ℂ A = ρ := by
  exact WeightedRootIntegralIdentity.weightedRootJumpEqualsConcreteResidue U L A ρ hU hL hres
