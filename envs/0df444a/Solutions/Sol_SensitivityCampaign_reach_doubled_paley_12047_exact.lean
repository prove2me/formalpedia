-- Prove2me | solution 1 for SensitivityCampaign.reach_doubled_paley_12047_exact
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T04:50:36.420706+00:00
-- url     : https://prove2.me/submissions/36e9a09f-ad1c-479b-a3d9-bc910cf125a0

import Mathlib
import Definitions.Def_SensitivityCampaign
import Theorems.Thm_SensitivityCampaign_reach_213519

theorem solution :
    SensitivityCampaign.AchievesExponent ((8 * Real.log (12047 : ℝ) / Real.log (2084175267334724 : ℝ)) : ℝ) := by
  have hpos : 0 < Real.log (2084175267334724 : ℝ) := Real.log_pos (by norm_num)
  have hle : 8 * Real.log (12047 : ℝ) / Real.log (2084175267334724 : ℝ) ≤ 213519 / 100000 := by
    rw [div_le_iff₀ hpos]
    have h1 : Real.log ((12047 : ℝ) ^ 120) ≤ Real.log ((2084175267334724 : ℝ) ^ 32) :=
      Real.log_le_log (by positivity) (by norm_num)
    rw [Real.log_pow, Real.log_pow] at h1
    push_cast at h1
    nlinarith
  intro ε hε S hS
  obtain ⟨n, f, hs, hb⟩ := SensitivityCampaign.reach_213519 ε hε S hS
  refine ⟨n, f, hs, le_trans ?_ hb⟩
  have h1 : (1 : ℝ) ≤ (OAI.Paper320.sensitivity f : ℝ) := by
    have : (2 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS
    have : (S : ℝ) ≤ (OAI.Paper320.sensitivity f : ℝ) := by exact_mod_cast hs
    linarith
  exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
