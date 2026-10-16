-- Prove2me | solution 1 for SensitivityCampaign.finite_certificate_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-15T18:27:16.947598+00:00
-- url     : https://prove2.me/submissions/d5a7b430-0fa0-45e8-a531-b5be8bf4e9b4

import Definitions.Def_SensitivityCampaign
import Theorems.Thm_SensitivityCampaign_finite_certificate
open OAI.Paper320

theorem solution
    {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool)
    (A B : ℕ) (hA : 1 < A) (hB : 1 < B)
    (hs : sensitivity f ≤ A) (hb : B ≤ blockSensitivityAt f x) :
    SensitivityCampaign.AchievesExponent
      (Real.log (B : ℝ) / Real.log (A : ℝ)) := by
  have hAr : (1 : ℝ) < A := by exact_mod_cast hA
  have hBr : (1 : ℝ) < B := by exact_mod_cast hB
  have hAp : (0 : ℝ) < A := by linarith
  have hBp : (0 : ℝ) < B := by linarith
  apply SensitivityCampaign.finite_certificate f x A B _ hA hB
    (div_nonneg (Real.log_pos hBr).le (Real.log_pos hAr).le) hs hb
  apply le_of_eq
  apply (Real.mul_log_eq_log_iff hAp hBp).mp
  exact div_mul_cancel₀ _ (ne_of_gt (Real.log_pos hAr))
