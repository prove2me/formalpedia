-- Prove2me | solution 1 for UnfairML.Coverage.eq_59
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T05:20:21.024023+00:00
-- url     : https://prove2.me/submissions/f50ccd38-7fe1-4bda-9b81-433f94fd8afc

import Mathlib
import Definitions.Def_UnfairML_Coverage_Model

open UnfairML.Coverage

theorem solution (P : Params) (hS : P.Standing) (hL : P.LowLoss) (σ : ℝ)
    (hσ : σ ∈ Set.Ico P.rho 1)
    (hcond : P.αp / P.βp ≤
      1 - (1 - (2 - σ) ^ 2 * σ ^ 2) / ((1 - σ ^ 2) * (2 - σ) ^ 2) * (P.γp / P.γr)) :
    Real.sqrt (P.βp * P.γp /
      (σ ^ 2 * P.βp * P.γp + (1 - σ ^ 2) * (P.βp * P.γr - P.αp * P.γr))) ≤ 2 - σ := by
  obtain ⟨hα, hβ, hdr, hdrp, hdp, hab, hgp, hgpr⟩ := hS
  simp only [Params.αp, Params.βp, Params.αr, Params.βr, Params.rho] at *
  obtain ⟨hσ1, hσ2⟩ := hσ
  have hgr : 0 < P.γr := by linarith
  have hrho : 1 / 2 < 1 / (2 - P.γp / P.γr) := by
    have : P.γp / P.γr < 1 := (div_lt_one hgr).2 hgpr
    have : 0 < P.γp / P.γr := div_pos hgp hgr
    rw [div_lt_div_iff₀ (by norm_num) (by linarith)]; linarith
  have hσ0 : 1 / 2 < σ := lt_of_lt_of_le hrho hσ1
  set αp := P.α * (1 - P.dp)
  set βp := P.β * P.dp
  have hβp : 0 < βp := mul_pos hβ (by linarith)
  have hgap : 0 < βp - αp := by
    have : P.β * P.dr - P.α * (1 - P.dr) ≥ 0 := by linarith
    have : (P.α + P.β) * (P.dp - P.dr) > 0 := mul_pos (by linarith) (by linarith)
    simp only [βp, αp]; nlinarith
  have h1s : 0 < 1 - σ ^ 2 := by nlinarith
  have h2s : 0 < (2 - σ) ^ 2 := by nlinarith
  have hD : 0 < σ ^ 2 * βp * P.γp + (1 - σ ^ 2) * (βp * P.γr - αp * P.γr) := by
    have : 0 < (1 - σ ^ 2) * ((βp - αp) * P.γr) := mul_pos h1s (mul_pos hgap hgr)
    have : 0 ≤ σ ^ 2 * βp * P.γp := by positivity
    nlinarith
  -- (55)-(57)
  set X := (1 - (2 - σ) ^ 2 * σ ^ 2) / ((1 - σ ^ 2) * (2 - σ) ^ 2)
  have h55 : X * (βp * P.γp) ≤ (βp - αp) * P.γr := by
    rw [div_le_iff₀ hβp] at hcond
    have h := mul_le_mul_of_nonneg_right hcond hgr.le
    have e : (1 - X * (P.γp / P.γr)) * βp * P.γr = βp * P.γr - X * (βp * P.γp) := by
      field_simp
    nlinarith
  have hXe : X * ((1 - σ ^ 2) * (2 - σ) ^ 2) = 1 - (2 - σ) ^ 2 * σ ^ 2 := by
    simp only [X]; exact div_mul_cancel₀ _ (mul_pos h1s h2s).ne'
  have h56 : (1 - (2 - σ) ^ 2 * σ ^ 2) * (βp * P.γp) ≤
      (1 - σ ^ 2) * (2 - σ) ^ 2 * ((βp - αp) * P.γr) := by
    rw [← hXe]
    have := mul_le_mul_of_nonneg_left h55 (le_of_lt (mul_pos h1s h2s))
    nlinarith
  have h58 : βp * P.γp / (σ ^ 2 * βp * P.γp + (1 - σ ^ 2) * (βp * P.γr - αp * P.γr)) ≤
      (2 - σ) ^ 2 := by
    rw [div_le_iff₀ hD]; nlinarith
  calc Real.sqrt _ ≤ Real.sqrt ((2 - σ) ^ 2) := Real.sqrt_le_sqrt h58
    _ = 2 - σ := Real.sqrt_sq (by linarith)
