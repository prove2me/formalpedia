-- Prove2me | solution 1 for Sendov.B10_11.P_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:22:02.871503+00:00
-- url     : https://prove2.me/submissions/03ce3885-9ef8-4eab-9fad-129f512d918a

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree10_11

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B10_11
set_option maxHeartbeats 2000000
namespace Sendov.B10_11
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 5) :
    0 < 32349375 + 39180105 * α + 10086687 * α ^ 2 - 24445935 * α ^ 3 + 11871036 * α ^ 4 - 351846 * α ^ 5 - 81598 * α ^ 6 - 4664 * α ^ 7 - 88 * α ^ 8 := by
  have hu : (0 : ℝ) ≤ 5 - α := by linarith
  have h0 : (0:ℝ) ≤ 32349375 * (5 - α) ^ 8 :=
    mul_nonneg (by norm_num) (pow_nonneg hu 8)
  have h1 : (0:ℝ) ≤ 454695525 * α ^ 1 * (5 - α) ^ 7 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 1)) (pow_nonneg hu 7)
  have h2 : (0:ℝ) ≤ 2529253350 * α ^ 2 * (5 - α) ^ 6 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 2)) (pow_nonneg hu 6)
  have h3 : (0:ℝ) ≤ 4382737200 * α ^ 3 * (5 - α) ^ 5 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 3)) (pow_nonneg hu 5)
  have h4 : (0:ℝ) ≤ 5044170375 * α ^ 4 * (5 - α) ^ 4 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 4)) (pow_nonneg hu 4)
  have h5 : (0:ℝ) ≤ 11732079375 * α ^ 5 * (5 - α) ^ 3 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 5)) (pow_nonneg hu 3)
  have h6 : (0:ℝ) ≤ 18187642400 * α ^ 6 * (5 - α) ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 6)) (pow_nonneg hu 2)
  have h7 : (0:ℝ) ≤ 11329113600 * α ^ 7 * (5 - α) ^ 1 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 7)) (pow_nonneg hu 1)
  have h8 : (0:ℝ) ≤ 2070835200 * α ^ 8 :=
    mul_nonneg (by norm_num) (pow_nonneg hα 8)
  have hid : (5 : ℝ) ^ 8 * (32349375 + 39180105 * α + 10086687 * α ^ 2 - 24445935 * α ^ 3 + 11871036 * α ^ 4 - 351846 * α ^ 5 - 81598 * α ^ 6 - 4664 * α ^ 7 - 88 * α ^ 8) = 32349375 * (5 - α) ^ 8 + 454695525 * α ^ 1 * (5 - α) ^ 7 + 2529253350 * α ^ 2 * (5 - α) ^ 6 + 4382737200 * α ^ 3 * (5 - α) ^ 5 + 5044170375 * α ^ 4 * (5 - α) ^ 4 + 11732079375 * α ^ 5 * (5 - α) ^ 3 + 18187642400 * α ^ 6 * (5 - α) ^ 2 + 11329113600 * α ^ 7 * (5 - α) ^ 1 + 2070835200 * α ^ 8 := by
    ring
  rcases le_total α (5 / (2 * 1)) with h | h
  · have hpos : (0 : ℝ) < 32349375 * (5 - α) ^ 8 :=
      mul_pos (by norm_num) (pow_pos (by linarith) 8)
    linarith
  · have hpos : (0 : ℝ) < 2070835200 * α ^ 8 :=
      mul_pos (by norm_num) (pow_pos (by linarith) 8)
    linarith
end Sendov.B10_11
