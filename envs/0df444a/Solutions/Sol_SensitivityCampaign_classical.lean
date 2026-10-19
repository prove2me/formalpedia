-- Prove2me | solution 1 for SensitivityCampaign.classical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-16T12:09:21.48874+00:00
-- url     : https://prove2.me/submissions/1111e85f-bfc3-47d3-8d2d-d2f9eebd7ff9

import Mathlib
import Definitions.Def_SensitivityCampaign
import Theorems.Thm_SensitivityCampaign_rubinstein_bounds
set_option maxHeartbeats 1000000

theorem solution : SensitivityCampaign.AchievesExponent (2 : ℝ) := by
  intro ε hε S hS
  obtain ⟨m, hm⟩ := exists_nat_gt (max (S : ℝ) ((2 : ℝ) ^ (1 / ε)))
  have hSm : (S : ℝ) < m := lt_of_le_of_lt (le_max_left _ _) hm
  have hSmN : S < m := by exact_mod_cast hSm
  have hm1 : 1 ≤ m := by omega
  obtain ⟨f, hs, hb⟩ := SensitivityCampaign.rubinstein_bounds m hm1
  refine ⟨(2*m)^2, f, ?_, ?_⟩
  · rw [hs]
    omega
  · have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hpow : (2 : ℝ) ≤ (2 * (m : ℝ)) ^ ε := by
      calc
        (2 : ℝ) = ((2 : ℝ) ^ (1 / ε)) ^ ε := by
          rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          rw [one_div_mul_cancel (ne_of_gt hε), Real.rpow_one]
        _ ≤ (2 * (m : ℝ)) ^ ε := by
          apply Real.rpow_le_rpow (by positivity) _ hε.le
          have hh := lt_of_le_of_lt (le_max_right (S : ℝ) ((2 : ℝ) ^ (1 / ε))) hm
          linarith
    rw [hs, hb]
    push_cast
    rw [Real.rpow_sub (by positivity), Real.rpow_two]
    apply (div_le_iff₀ (Real.rpow_pos_of_pos (by positivity) ε)).mpr
    have hh := mul_le_mul_of_nonneg_left hpow (sq_nonneg (m : ℝ))
    nlinarith
