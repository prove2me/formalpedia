-- Prove2me | solution 1 for SystemSqueeze.Accommodation.threshold_nine
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:04:40.823548+00:00
-- url     : https://prove2.me/submissions/bb1f7b51-0ed8-4f60-8b52-ee82455ccfe4

import Mathlib
import Definitions.Def_SystemSqueeze_Accommodation_Model
set_option autoImplicit false
open SystemSqueeze.Accommodation

theorem solution (UC UI γ : ℝ) (hUI : 0 < UI) (hlt : UI < UC) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) :
    ((UC - γ * UI) * (2 * UC + γ * UI) / (18 * (1 + γ) * (1 - γ)) ≥ UC ^ 2 / 9 ↔
        γ ≥ UC * UI / (2 * UC ^ 2 - UI ^ 2)) ∧
      UC * UI / (2 * UC ^ 2 - UI ^ 2) < gammaMax UC UI := by
  have hUC : 0 < UC := by linarith
  have hD : 0 < 2 * UC ^ 2 - UI ^ 2 := by nlinarith
  have hden : 0 < 18 * (1 + γ) * (1 - γ) := by
    have : 0 < 1 + γ := by linarith
    have : 0 < 1 - γ := by linarith
    positivity
  constructor
  · rw [ge_iff_le, ge_iff_le, le_div_iff₀ hden, div_le_iff₀ hD]
    have key : (UC - γ * UI) * (2 * UC + γ * UI) - UC ^ 2 / 9 * (18 * (1 + γ) * (1 - γ)) =
        γ * (γ * (2 * UC ^ 2 - UI ^ 2) - UC * UI) := by ring
    constructor
    · intro h
      by_contra hc
      push_neg at hc
      have : γ * (γ * (2 * UC ^ 2 - UI ^ 2) - UC * UI) < 0 := mul_neg_of_pos_of_neg hγ0 (by linarith)
      linarith
    · intro h
      have : 0 ≤ γ * (γ * (2 * UC ^ 2 - UI ^ 2) - UC * UI) := mul_nonneg hγ0.le (by linarith)
      linarith
  · unfold gammaMax
    rw [div_lt_div_iff₀ hD hUI]
    set s := Real.sqrt (UC ^ 2 + 3 * UI ^ 2) with hs
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs2 : s ^ 2 = UC ^ 2 + 3 * UI ^ 2 := Real.sq_sqrt (by positivity)
    have h1 : 2 * UC ^ 3 < s * (2 * UC ^ 2 - UI ^ 2) := by
      by_contra hc
      push_neg at hc
      have h0 : 0 ≤ s * (2 * UC ^ 2 - UI ^ 2) := mul_nonneg hs0 hD.le
      have h2 : (s * (2 * UC ^ 2 - UI ^ 2)) ^ 2 ≤ (2 * UC ^ 3) ^ 2 := by
        apply pow_le_pow_left₀ h0 hc
      have h3 : (s * (2 * UC ^ 2 - UI ^ 2)) ^ 2 = (UC ^ 2 + 3 * UI ^ 2) * (2 * UC ^ 2 - UI ^ 2) ^ 2 := by
        rw [mul_pow, hs2]
      rw [h3] at h2
      have h4 : (UC ^ 2 + 3 * UI ^ 2) * (2 * UC ^ 2 - UI ^ 2) ^ 2 - (2 * UC ^ 3) ^ 2 =
          UI ^ 2 * (8 * UC ^ 2 - 3 * UI ^ 2) * (UC ^ 2 - UI ^ 2) := by ring
      have h5 : 0 < UI ^ 2 * (8 * UC ^ 2 - 3 * UI ^ 2) * (UC ^ 2 - UI ^ 2) := by
        have a1 : 0 < UI ^ 2 := by positivity
        have a2 : 0 < 8 * UC ^ 2 - 3 * UI ^ 2 := by nlinarith
        have a3 : 0 < UC ^ 2 - UI ^ 2 := by nlinarith
        positivity
      linarith
    nlinarith [h1]
