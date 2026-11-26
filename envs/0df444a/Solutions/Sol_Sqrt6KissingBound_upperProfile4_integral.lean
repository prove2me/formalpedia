-- Prove2me | solution 1 for Sqrt6KissingBound.upperProfile4_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:23:03.178033+00:00
-- url     : https://prove2.me/submissions/df12df93-1fde-4315-ac4f-4b950cf025d9

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionFour
import Theorems.Thm_Sqrt6KissingBound_inner_standardAxis_standardCoordinates
import Theorems.Thm_Sqrt6KissingBound_mem_tailBall
import Theorems.Thm_Sqrt6KissingBound_norm_standardAxis
attribute [local simp] Sqrt6KissingBound.inner_standardAxis_standardCoordinates
attribute [local simp] Sqrt6KissingBound.mem_tailBall
attribute [local simp] Sqrt6KissingBound.norm_standardAxis


section
namespace Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
set_option maxHeartbeats 800000
private lemma s3_sq : s3_d4 ^ 2 = 3 := by norm_num [s3_d4]
end
end Sqrt6KissingBound
end

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
set_option maxHeartbeats 800000
namespace Sqrt6KissingBound
theorem _root_.solution :
    (∫ t in a_d4..1, upperProfile4 t ^ 3) = (33169 - 19150 * s3_d4) / 40 := by
  let B : ℝ := 2 - 6 * s3_d4
  let C : ℝ := 12 + 6 * s3_d4
  have hfun : (fun t : ℝ => upperProfile4 t ^ 3) = fun t =>
      (-14 : ℝ) ^ 3 * t ^ 6 + 3 * (-14 : ℝ) ^ 2 * C * t ^ 5 +
      (3 * (-14 : ℝ) ^ 2 * B + 3 * (-14 : ℝ) * C ^ 2) * t ^ 4 +
      (C ^ 3 + 6 * (-14 : ℝ) * C * B) * t ^ 3 +
      (3 * C ^ 2 * B + 3 * (-14 : ℝ) * B ^ 2) * t ^ 2 +
      3 * C * B ^ 2 * t ^ 1 + B ^ 3 := by
    funext t
    dsimp [upperProfile4, B, C]
    ring
  rw [hfun]
  simp (disch := (apply Continuous.intervalIntegrable; fun_prop)) only
    [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      integral_pow, intervalIntegral.integral_const, smul_eq_mul]
  dsimp [a_d4, B, C]
  have h3 := congrArg (fun x : ℝ => x * s3_d4) s3_sq
  have h4 := congrArg (fun x : ℝ => x ^ 2) s3_sq
  have h5 := congrArg (fun x : ℝ => x * s3_d4) h4
  have h6 := congrArg (fun x : ℝ => x ^ 3) s3_sq
  have h7 := congrArg (fun x : ℝ => x * s3_d4) h6
  ring_nf
  nlinarith [s3_sq, h3, h4, h5, h6, h7]
end Sqrt6KissingBound
