-- Prove2me | solution 1 for SensitivityCampaign.reach_2127294
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-20T18:38:41.687314+00:00
-- url     : https://prove2.me/submissions/3f503859-0d48-410d-8ece-e058007a0885

import Mathlib
import Definitions.Def_SensitivityCampaign
import Theorems.Thm_SensitivityCampaign_reach_21303_gamma

set_option autoImplicit false

/- The accepted exponent 2.1303 implies this lower target by enlarging the
   positive exponent loss. No new Boolean construction is needed. -/
theorem solution : SensitivityCampaign.AchievesExponent (2.127294 : ℝ) := by
  intro ε hε S hS
  have hδ : 0 < ε + ((2.1303 : ℝ) - 2.127294) := by linarith
  obtain ⟨n, f, hs, hb⟩ := SensitivityCampaign.reach_21303_gamma
    (ε + ((2.1303 : ℝ) - 2.127294)) hδ S hS
  refine ⟨n, f, hs, ?_⟩
  have he : (2.1303 : ℝ) - (ε + ((2.1303 : ℝ) - 2.127294)) =
      (2.127294 : ℝ) - ε := by ring
  simpa only [he] using hb
