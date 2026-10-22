-- Prove2me | solution 1 for SuspensionContract.HighCostC2.lemma_EC_2_vi_equiv
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:49:14.628417+00:00
-- url     : https://prove2.me/submissions/e8d55fb6-cc28-4e1e-92e1-cdd623e3a049

import Mathlib
import Definitions.Def_SuspensionContract_HighCostC2_Setting

set_option autoImplicit false
open SuspensionContract.HighCostC2

theorem solution (P : Params) (hP : P.Standing) (hρ : P.r + P.μ < P.ρ) :
    P.vlow ≤ P.Vbar - (P.ρ - P.r) / (P.ρ - P.r - P.μ) * P.wbar ↔ P.Rhat ≤ P.R := by
  obtain ⟨⟨hμl0, hμlμ⟩, ⟨hb0, hbc⟩, hK, ⟨hr0, hrρ⟩, hass⟩ := hP
  have hΔ : 0 < P.μ - P.μlow := by linarith
  have hρ0 : 0 < P.ρ := by linarith
  have hd : 0 < P.ρ - P.r - P.μ := by linarith
  have key : P.Vbar - (P.ρ - P.r) / (P.ρ - P.r - P.μ) * P.wbar - P.vlow
      = (P.R - P.Rhat) * (P.μ - P.μlow) / P.r := by
    unfold Params.Vbar Params.vlow Params.wbar Params.Rhat Params.β Params.Δμ
    field_simp
    ring
  constructor
  · intro h
    have h1 : 0 ≤ P.Vbar - (P.ρ - P.r) / (P.ρ - P.r - P.μ) * P.wbar - P.vlow := by linarith
    rw [key] at h1
    have h2 : 0 ≤ (P.R - P.Rhat) * (P.μ - P.μlow) := by
      have := mul_nonneg h1 hr0.le
      rwa [div_mul_cancel₀ _ hr0.ne'] at this
    have h3 : 0 ≤ P.R - P.Rhat := by
      by_contra hneg
      push_neg at hneg
      nlinarith
    linarith
  · intro h
    have h1 : 0 ≤ P.R - P.Rhat := by linarith
    have : 0 ≤ P.Vbar - (P.ρ - P.r) / (P.ρ - P.r - P.μ) * P.wbar - P.vlow := by
      rw [key]; positivity
    linarith
