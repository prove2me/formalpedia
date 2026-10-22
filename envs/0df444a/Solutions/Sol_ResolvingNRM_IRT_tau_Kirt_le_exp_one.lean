-- Prove2me | solution 1 for ResolvingNRM.IRT.tau_Kirt_le_exp_one
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:02:25.881277+00:00
-- url     : https://prove2.me/submissions/82bfa682-380c-4177-a0c1-d79185f95d77

import Mathlib
import Definitions.Def_RLPBidPrice_Unbiased_Model
import Definitions.Def_ResolvingNRM_IRT_Model
set_option autoImplicit false
open RLPBidPrice.Unbiased Matrix
open ResolvingNRM.IRT

theorem solution (T : ℝ) (hT : 1 ≤ T) :
    T ^ ((5 / 6 : ℝ) ^ Kirt T) ≤ Real.exp 1 := by
  have hT0 : 0 < T := by linarith
  rw [Real.rpow_def_of_pos hT0]
  apply Real.exp_le_exp.2
  rw [mul_comm]
  set L := Real.log T with hL
  have hL0 : 0 ≤ L := Real.log_nonneg hT
  have hs1 : (5 / 6 : ℝ) ^ Kirt T ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  by_cases hL1 : L ≤ 1
  · nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 5/6) (Kirt T)]
  · push_neg at hL1
    have hlogL : 0 < Real.log L := Real.log_pos hL1
    have hl65 : 0 < Real.log (6 / 5 : ℝ) := Real.log_pos (by norm_num)
    have hK : Real.log L / Real.log (6 / 5) ≤ (Kirt T : ℝ) := Nat.le_ceil _
    have hK' : Real.log L ≤ (Kirt T : ℝ) * Real.log (6 / 5) := by
      rwa [div_le_iff₀ hl65] at hK
    have h1 : L ≤ (6 / 5 : ℝ) ^ Kirt T := by
      calc L = Real.exp (Real.log L) := (Real.exp_log (by linarith)).symm
        _ ≤ Real.exp ((Kirt T : ℝ) * Real.log (6 / 5)) := Real.exp_le_exp.2 hK'
        _ = (6 / 5 : ℝ) ^ Kirt T := by
          rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    have h2 : (5 / 6 : ℝ) ^ Kirt T * (6 / 5 : ℝ) ^ Kirt T = 1 := by
      rw [← mul_pow]; norm_num
    calc (5 / 6 : ℝ) ^ Kirt T * L ≤ (5 / 6 : ℝ) ^ Kirt T * (6 / 5 : ℝ) ^ Kirt T :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1 := h2
