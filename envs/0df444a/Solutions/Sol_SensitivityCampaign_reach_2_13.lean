-- Prove2me | solution 1 for SensitivityCampaign.reach_2_13
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-20T18:38:44.814869+00:00
-- url     : https://prove2.me/submissions/d2ed74fd-651b-4df7-bcf8-eba13ef4a0ae

import Mathlib
import Definitions.Def_SensitivityCampaign
import Theorems.Thm_SensitivityCampaign_reach_21303_gamma

set_option autoImplicit false

/- The accepted exponent 2.1303 implies this lower target by enlarging the
   positive exponent loss. No new Boolean construction is needed. -/
theorem solution : SensitivityCampaign.AchievesExponent (2.13 : ℝ) := by
  intro ε hε S hS
  have hδ : 0 < ε + ((2.1303 : ℝ) - 2.13) := by linarith
  obtain ⟨n, f, hs, hb⟩ := SensitivityCampaign.reach_21303_gamma
    (ε + ((2.1303 : ℝ) - 2.13)) hδ S hS
  refine ⟨n, f, hs, ?_⟩
  have he : (2.1303 : ℝ) - (ε + ((2.1303 : ℝ) - 2.13)) =
      (2.13 : ℝ) - ε := by ring
  simpa only [he] using hb
