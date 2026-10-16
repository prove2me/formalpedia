-- Prove2me | solution 1 for SensitivityCampaign.baseline
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-15T18:27:20.109168+00:00
-- url     : https://prove2.me/submissions/9530558c-7034-4bca-bb5d-1859362d8ae5

import Definitions.Def_SensitivityCampaign
import Theorems.Thm_SensitivityCampaign_finite_certificate
import Theorems.Thm_SensitivityCampaign_openai_seed_bounds
import Theorems.Thm_SensitivityCampaign_baseline_arithmetic
open OAI.Paper320

theorem solution : SensitivityCampaign.AchievesExponent (2.000252407 : ℝ) := by
  let M : ℕ := 9 ^ 10
  obtain ⟨n, f, _, hs, hb⟩ := SensitivityCampaign.openai_seed_bounds 9 M (by norm_num) (by rfl)
  apply SensitivityCampaign.finite_certificate f (fun _ => false)
    (2 * (9 + 2) * M ^ 10) (M ^ 2 * (2 * M ^ 2 + 1) ^ 9) (2.000252407 : ℝ)
  · norm_num [M]
  · norm_num [M]
  · norm_num
  · exact hs
  · exact hb
  · exact SensitivityCampaign.baseline_arithmetic
