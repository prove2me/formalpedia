-- Prove2me | solution 1 for Sqrt6KissingBound.upperProfile4_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:22:04.158195+00:00
-- url     : https://prove2.me/submissions/0876899d-9bfc-4317-94d3-facbda5ff3a0

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
private lemma s3_pos : 0 < s3_d4 := Real.sqrt_pos.2 (by norm_num)
private lemma s3_sq : s3_d4 ^ 2 = 3 := by norm_num [s3_d4]
private lemma q4_nonneg {t : ℝ} (hta : a_d4 ≤ t) :
    0 ≤ 196 * t ^ 2 - (140 + 70 * s3_d4) * t - 48 + 74 * s3_d4 := by
  have hs15 : (3 : ℝ) / 2 < s3_d4 := by
    have hs0 : 0 ≤ s3_d4 := s3_pos.le
    nlinarith [s3_sq]
  have hs109 : (10 : ℝ) / 9 < s3_d4 := by linarith
  have hbase : 0 ≤ -6 + 4 * s3_d4 := by linarith
  have hfactor : 0 ≤ 196 * (t + a_d4) - (140 + 70 * s3_d4) := by
    dsimp [a_d4] at hta ⊢
    nlinarith
  have hprod : 0 ≤ (t - a_d4) * (196 * (t + a_d4) - (140 + 70 * s3_d4)) :=
    mul_nonneg (sub_nonneg.mpr hta) hfactor
  have hid :
      196 * t ^ 2 - (140 + 70 * s3_d4) * t - 48 + 74 * s3_d4 =
        (-6 + 4 * s3_d4) + (t - a_d4) * (196 * (t + a_d4) - (140 + 70 * s3_d4)) := by
    dsimp [a_d4]
    nlinarith [s3_sq]
  rw [hid]
  positivity
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
theorem _root_.solution {t : ℝ} (hta : a_d4 ≤ t) (ht1 : t ≤ 1) :
    upperProfile4 t ^ 2 ≤ 1 - t ^ 2 := by
  let h : ℝ := 14 * t + 2 - 6 * s3_d4
  let q : ℝ := 196 * t ^ 2 - (140 + 70 * s3_d4) * t - 48 + 74 * s3_d4
  have hq : 0 ≤ q := by simpa [q] using q4_nonneg hta
  have hP : 0 ≤ 1 + t - (1 - t) * h ^ 2 := by
    have hid : 1 + t - (1 - t) * h ^ 2 = (t - a_d4) * q := by
      dsimp [h, q, a_d4]
      linear_combination (t + 1) * s3_sq
    rw [hid]
    exact mul_nonneg (sub_nonneg.mpr hta) hq
  have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hid2 : 1 - t ^ 2 - upperProfile4 t ^ 2 =
      (1 - t) * (1 + t - (1 - t) * h ^ 2) := by
    dsimp [upperProfile4, h]
    ring
  have hnonneg := mul_nonneg h1t hP
  rw [← hid2] at hnonneg
  linarith
end Sqrt6KissingBound
