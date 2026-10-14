-- Prove2me | solution 1 for ThreeSum1960614.initial_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-14T07:17:40.668377+00:00
-- url     : https://prove2.me/submissions/25a37a8a-a911-4afd-87f5-81ce12d8f7bd

import Theorems.Thm_ThreeSum1960614_high_precision_logs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
open ThreeSum1960614

theorem solution : entropy theta < (244168414687344 / 1000000000000000 : ℝ) := by
  obtain ⟨hl, _, _, _, hx, hy⟩ := ThreeSum1960614.high_precision_logs
  have hln : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hθ : theta ≠ 0 := by norm_num [theta]
  have h1 : 1 - theta ≠ 0 := by norm_num [theta]
  have h32 : Real.log (32 : ℝ) = 5 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 5
    norm_num at h
    exact h
  have hlogθ : Real.log theta = Real.log (32 * theta) - 5 * Real.log 2 := by
    rw [Real.log_mul (by norm_num : (32 : ℝ) ≠ 0) hθ, h32]
    ring
  have hlog1 : Real.log (1 - theta) = Real.log (2 * (1 - theta)) - Real.log 2 := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) h1]
    ring
  have heq : entropy theta =
      (-theta * Real.log theta - (1 - theta) * Real.log (1 - theta)) / Real.log 2 := by
    simp only [entropy, Real.binEntropy, Real.log_inv]
    ring
  rw [heq, div_lt_iff₀ hln, hlogθ, hlog1]
  have hn : (1 + 4 * theta - (244168414687344 / 1000000000000000 : ℝ)) *
      (6931471805599453094173 / 10^22) <
      theta * (2570554035235070921259 / 10^22) +
        (1 - theta) * (6518981167335747474116 / 10^22) := by norm_num [theta]
  dsimp [theta] at *
  nlinarith only [hl.2, hx.1, hy.1, hn]
