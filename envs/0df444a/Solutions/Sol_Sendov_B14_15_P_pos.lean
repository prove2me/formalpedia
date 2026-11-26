-- Prove2me | solution 1 for Sendov.B14_15.P_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:24:15.848526+00:00
-- url     : https://prove2.me/submissions/7d5df417-b50e-4b5b-b6ad-2b439df83214

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree14_15

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B14_15
set_option maxHeartbeats 2000000
namespace Sendov.B14_15
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 7) :
    0 < 4540012290450 + 9000770719122 * α + 7217967952260 * α ^ 2 + 2789503991820 * α ^ 3 + 226924812075 * α ^ 4 - 867448623285 * α ^ 5 + 235182487819 * α ^ 6 + 1315276135 * α ^ 7 - 765536900 * α ^ 8 - 78585080 * α ^ 9 - 3463520 * α ^ 10 - 74480 * α ^ 11 - 640 * α ^ 12 := by
  have hu : (0 : ℝ) ≤ 7 - α := by linarith
  have h0 : (0:ℝ) ≤ 4540012290450 * (7 - α) ^ 12 :=
    mul_nonneg (by norm_num) (pow_nonneg hu 12)
  have h1 : (0:ℝ) ≤ 117485542519254 * α ^ 1 * (7 - α) ^ 11 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 1)) (pow_nonneg hu 11)
  have h2 : (0:ℝ) ≤ 1346380586202834 * α ^ 2 * (7 - α) ^ 10 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 2)) (pow_nonneg hu 10)
  have h3 : (0:ℝ) ≤ 8957703596562630 * α ^ 3 * (7 - α) ^ 9 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 3)) (pow_nonneg hu 9)
  have h4 : (0:ℝ) ≤ 37714860895632375 * α ^ 4 * (7 - α) ^ 8 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 4)) (pow_nonneg hu 8)
  have h5 : (0:ℝ) ≤ 91053479724275985 * α ^ 5 * (7 - α) ^ 7 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 5)) (pow_nonneg hu 7)
  have h6 : (0:ℝ) ≤ 128817765797828254 * α ^ 6 * (7 - α) ^ 6 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 6)) (pow_nonneg hu 6)
  have h7 : (0:ℝ) ≤ 133833540832996984 * α ^ 7 * (7 - α) ^ 5 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 7)) (pow_nonneg hu 5)
  have h8 : (0:ℝ) ≤ 161773229978174745 * α ^ 8 * (7 - α) ^ 4 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 8)) (pow_nonneg hu 4)
  have h9 : (0:ℝ) ≤ 197834312331965435 * α ^ 9 * (7 - α) ^ 3 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 9)) (pow_nonneg hu 3)
  have h10 : (0:ℝ) ≤ 152113356071582990 * α ^ 10 * (7 - α) ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 10)) (pow_nonneg hu 2)
  have h11 : (0:ℝ) ≤ 57359456154000000 * α ^ 11 * (7 - α) ^ 1 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 11)) (pow_nonneg hu 1)
  have h12 : (0:ℝ) ≤ 7376986416800000 * α ^ 12 :=
    mul_nonneg (by norm_num) (pow_nonneg hα 12)
  have hid : (7 : ℝ) ^ 12 * (4540012290450 + 9000770719122 * α + 7217967952260 * α ^ 2 + 2789503991820 * α ^ 3 + 226924812075 * α ^ 4 - 867448623285 * α ^ 5 + 235182487819 * α ^ 6 + 1315276135 * α ^ 7 - 765536900 * α ^ 8 - 78585080 * α ^ 9 - 3463520 * α ^ 10 - 74480 * α ^ 11 - 640 * α ^ 12) = 4540012290450 * (7 - α) ^ 12 + 117485542519254 * α ^ 1 * (7 - α) ^ 11 + 1346380586202834 * α ^ 2 * (7 - α) ^ 10 + 8957703596562630 * α ^ 3 * (7 - α) ^ 9 + 37714860895632375 * α ^ 4 * (7 - α) ^ 8 + 91053479724275985 * α ^ 5 * (7 - α) ^ 7 + 128817765797828254 * α ^ 6 * (7 - α) ^ 6 + 133833540832996984 * α ^ 7 * (7 - α) ^ 5 + 161773229978174745 * α ^ 8 * (7 - α) ^ 4 + 197834312331965435 * α ^ 9 * (7 - α) ^ 3 + 152113356071582990 * α ^ 10 * (7 - α) ^ 2 + 57359456154000000 * α ^ 11 * (7 - α) ^ 1 + 7376986416800000 * α ^ 12 := by
    ring
  rcases le_total α (7 / (2 * 1)) with h | h
  · have hpos : (0 : ℝ) < 4540012290450 * (7 - α) ^ 12 :=
      mul_pos (by norm_num) (pow_pos (by linarith) 12)
    linarith
  · have hpos : (0 : ℝ) < 7376986416800000 * α ^ 12 :=
      mul_pos (by norm_num) (pow_pos (by linarith) 12)
    linarith
end Sendov.B14_15
