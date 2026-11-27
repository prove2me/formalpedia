-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_EffectiveHS_lift_constants_le_910cce236f40
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:54:44.819829+00:00
-- url     : https://prove2.me/submissions/361d2d87-920c-405c-868f-da1714c96d1a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PConstants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PDivision
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_cD_pos_7b8ed93f5d7d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_cD_le_1c08ca7d6cd0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_half_log_add_le_half_log_885b1995f26a


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.EffectiveHS
open Finset
open Real
namespace GroundTheory.Heights₂.Heights.EffectiveHS
theorem _root_.solution (D : ℕ) (hD : 1 ≤ D) (ρ ρ₁ T C : ℝ) (hρ : 2 ^ 26 ≤ ρ)
    (hDρ : (D : ℝ) ≤ ρ) (h1 : 1 ≤ ρ₁) (h1ρ : ρ₁ ≤ ρ) (hT : 1 ≤ T) (hC : 26 ≤ C) :
    2 * D * log ρ₁ + D * log (Real.sqrt D * ρ₁) + (1 / 2) * log (140 * cD D * T ^ D) ≤
        4 * D * log (ρ * T) ∧
      4 * D * log (ρ * T) ≤ C * D ^ 2 * log (ρ * T) := by
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hρ0 : 0 < ρ := lt_of_lt_of_le (by norm_num) hρ
  have hρ₁0 : 0 < ρ₁ := lt_of_lt_of_le one_pos h1
  have hT0 : 0 < T := lt_of_lt_of_le one_pos hT
  have hlogT : 0 ≤ log T := log_nonneg hT
  have hlogρ₁ : log ρ₁ ≤ log ρ := log_le_log hρ₁0 h1ρ
  have hlogD : log D ≤ log ρ := log_le_log (by linarith) hDρ
  have hlogD0 : 0 ≤ log (D : ℝ) := log_nonneg hD'
  have hlogρ₁0 : 0 ≤ log ρ₁ := log_nonneg h1
  obtain ⟨hc1, hc2⟩ := half_log_add_le_half_log (D : ℝ) ρ hD' hρ
  have hcD := cD_pos D
  have hcDle : log (cD D) ≤ log 2 + D * log (2 * π) := by
    have h := log_le_log hcD (cD_le D)
    rwa [log_mul (by norm_num) (by positivity), log_pow] at h
  have hsplit : log (140 * cD D * T ^ D) = log 140 + log (cD D) + D * log T := by
    rw [log_mul (by positivity) (by positivity), log_mul (by norm_num) hcD.ne', log_pow]
  have h280 : log 280 = log 140 + log 2 := by
    rw [← log_mul (by norm_num) (by norm_num)]; norm_num
  have hsq : log (Real.sqrt D * ρ₁) = log D / 2 + log ρ₁ := by
    rw [log_mul (by positivity) hρ₁0.ne', log_sqrt (by positivity)]
  have hρT : log (ρ * T) = log ρ + log T := log_mul hρ0.ne' hT0.ne'
  have hlogρ : 0 ≤ log ρ := log_nonneg (by linarith)
  refine ⟨?_, ?_⟩
  · rw [hsplit, hsq, hρT]
    have e1 : (D : ℝ) * log ρ₁ ≤ D * log ρ := mul_le_mul_of_nonneg_left hlogρ₁ (by linarith)
    have e2 : (D : ℝ) * log D ≤ D * log ρ := mul_le_mul_of_nonneg_left hlogD (by linarith)
    have e3 : (D : ℝ) * log T ≥ 0 := mul_nonneg (by linarith) hlogT
    nlinarith
  · rw [hρT]
    have hL : 0 ≤ log ρ + log T := by linarith
    have hDD : 4 * (D : ℝ) ≤ C * D ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right hDD hL
end GroundTheory.Heights₂.Heights.EffectiveHS
