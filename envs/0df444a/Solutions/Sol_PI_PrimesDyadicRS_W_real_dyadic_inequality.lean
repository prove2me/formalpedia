-- Prove2me | solution 1 for PI.PrimesDyadicRS.W.real_dyadic_inequality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:05:35.972654+00:00
-- url     : https://prove2.me/submissions/85063cf4-7673-4e78-8a09-f06d7c6118e5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_ThetaDiff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_RealIneq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.PrimesDyadicRS PI.PrimesDyadicRS.W
namespace PI.PrimesDyadicRS.W
theorem _root_.solution : RealIneq := by
  intro y hy
  have hy0 : 0 < y := by linarith
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl2' : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have hL16 : 16 * Real.log 2 ≤ Real.log y := by
    have e : Real.log 65536 = 16 * Real.log 2 := by
      rw [show (65536 : ℝ) = 2 ^ 16 by norm_num, Real.log_pow]; norm_num
    rw [← e]; exact Real.log_le_log (by norm_num) hy
  have hLpos : 0 < Real.log y := by linarith
  have hlog2y : Real.log (2 * y) = Real.log 2 + Real.log y := Real.log_mul (by norm_num) hy0.ne'
  have hs : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy0.le
  have hs256 : (256 : ℝ) ≤ Real.sqrt y := by
    have e : Real.sqrt 65536 = 256 := by
      rw [show (65536 : ℝ) = 256 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← e]; exact Real.sqrt_le_sqrt hy
  have hsq2 : Real.sqrt (2 * y) = Real.sqrt 2 * Real.sqrt y := Real.sqrt_mul (by norm_num) y
  have hsqrt2 : Real.sqrt 2 < 1.4143 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hlogsq : Real.log (Real.sqrt (2 * y)) = (Real.log 2 + Real.log y) / 2 := by
    rw [Real.log_sqrt (by positivity), hlog2y]
  have hspos : 0 < Real.sqrt y := by linarith
  have hLs : Real.log y = 2 * Real.log (Real.sqrt y) := by
    conv_lhs => rw [← hs]
    rw [Real.log_mul hspos.ne' hspos.ne']; ring
  have hlogs : Real.log (Real.sqrt y) ≤ 8 * Real.log 2 + Real.sqrt y / 256 - 1 := by
    have h := Real.log_le_sub_one_of_pos (x := Real.sqrt y / 256) (by positivity)
    rw [Real.log_div hspos.ne' (by norm_num), show (256 : ℝ) = 2 ^ 8 by norm_num,
      Real.log_pow] at h
    push_cast at h
    linarith
  have hLup : Real.log y ≤ 9.1 + Real.sqrt y / 128 := by linarith
  have hMup : Real.log 2 + Real.log y ≤ 9.8 + Real.sqrt y / 128 := by linarith
  have hL2 : Real.log y ^ 2 ≤ (9.1 + Real.sqrt y / 128) ^ 2 :=
    pow_le_pow_left₀ hLpos.le hLup 2
  have hM2 : (Real.log 2 + Real.log y) ^ 2 ≤ (9.8 + Real.sqrt y / 128) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hMup 2
  have hLHS : 3 * y / (5 * Real.log y) * Real.log (2 * y)
      = 3 / 5 * y + 3 / 5 * (y * (Real.log 2 / Real.log y)) := by
    rw [hlog2y]; field_simp; ring
  have hratio : Real.log 2 / Real.log y ≤ 1 / 16 := by
    rw [div_le_iff₀ hLpos]; linarith
  have hyr : y * (Real.log 2 / Real.log y) ≤ y * (1 / 16) :=
    mul_le_mul_of_nonneg_left hratio hy0.le
  have hs2 : Real.sqrt 2 * Real.sqrt y ≤ 1.4143 * Real.sqrt y :=
    mul_le_mul_of_nonneg_right hsqrt2.le hspos.le
  have hq : 0 ≤ (Real.sqrt y - 256) * Real.sqrt y :=
    mul_nonneg (by linarith) hspos.le
  rw [hLHS, hlogsq, hsq2, hlog2y, div_pow]
  norm_num
  nlinarith [hL2, hM2, hs2, hq, hyr, hs, hl2, hl2', hLpos, hspos]
end PI.PrimesDyadicRS.W
