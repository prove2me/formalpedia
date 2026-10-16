-- Prove2me | solution 1 for SensitivityCampaign.reach_20205
-- status  : ACCEPTED   (prove)
-- author  : @Leo Shaposhnik
-- created : 2026-10-16T00:11:23.491393+00:00
-- url     : https://prove2.me/submissions/cf267e8b-68d1-4d7a-8366-9da5dcf88a33

import Mathlib
import Definitions.Def_SensitivityCampaign
import Theorems.Thm_SensitivityCampaign_finite_certificate
import Theorems.Thm_SensitivityCampaign_finite_certificate_log
import Definitions.Def_BS20205_Sharp_Arithmetic
import Theorems.Thm_OAI_Paper320_finite_certificate_20205

open OAI.Paper320
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem solution : SensitivityCampaign.AchievesExponent (2.0205 : ℝ) := by
  obtain ⟨n, f, hn, hz, hs, hb, hA, hBA, hgap⟩ := finite_certificate_20205
  have hB : 1 < sharpB := by nlinarith
  have hAp : 0 < (sharpA : ℝ) := by
    exact_mod_cast (show 0 < sharpA by omega)
  have hBp : 0 < (sharpB : ℝ) := by exact_mod_cast (show 0 < sharpB by omega)
  have hgapR : (sharpA : ℝ)^4041 < (sharpB : ℝ)^2000 := by exact_mod_cast hgap
  have hlog := Real.log_lt_log (pow_pos hAp 4041) hgapR
  rw [Real.log_pow, Real.log_pow] at hlog
  have hpower : (sharpA : ℝ) ^ (2.0205 : ℝ) ≤ (sharpB : ℝ) := by
    rw [Real.rpow_def_of_pos hAp, ← Real.exp_log hBp]
    apply Real.exp_le_exp.mpr
    norm_num only [Nat.cast_ofNat] at hlog
    linarith
  exact SensitivityCampaign.finite_certificate f (fun _ => false)
    sharpA sharpB (2.0205 : ℝ) hA hB (by norm_num) hs hb hpower
