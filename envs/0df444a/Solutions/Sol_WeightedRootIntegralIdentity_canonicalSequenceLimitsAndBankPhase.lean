-- Prove2me | solution 1 for WeightedRootIntegralIdentity.canonicalSequenceLimitsAndBankPhase
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-20T10:57:37.72813+00:00
-- url     : https://prove2.me/submissions/1a1bb8cc-cc22-4d5b-82ba-1951a3117007

import Mathlib
open Filter Topology

theorem solution
    (VR VL I O : ℕ → ℂ) (upper lower M : ℂ) (theta : ℝ)
    (hVR : Tendsto VR atTop (𝓝 0))
    (hVL : Tendsto VL atTop (𝓝 0))
    (hI : Tendsto I atTop (𝓝 0))
    (hO : Tendsto O atTop (𝓝 0))
    (hphase : upper - lower = 2 * Complex.I * (Real.sin theta : ℂ) * M) :
    Tendsto VR atTop (𝓝 0) ∧ Tendsto VL atTop (𝓝 0) ∧
      Tendsto I atTop (𝓝 0) ∧ Tendsto O atTop (𝓝 0) ∧
      upper - lower = 2 * Complex.I * (Real.sin theta : ℂ) * M := by
  exact ⟨hVR, hVL, hI, hO, hphase⟩
