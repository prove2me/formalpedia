-- Prove2me | solution 1 for Sendov.B12_13.P_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:23:03.108334+00:00
-- url     : https://prove2.me/submissions/a9d90000-c53a-4253-b932-00a088dade55

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree12_13

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B12_13
set_option maxHeartbeats 2000000
namespace Sendov.B12_13
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 6) :
    0 < 67214552328 + 108758874312 * α + 64248083658 * α ^ 2 + 8893434528 * α ^ 3 - 26471207052 * α ^ 4 + 9402730740 * α ^ 5 - 77587159 * α ^ 6 - 46242248 * α ^ 7 - 3634800 * α ^ 8 - 118976 * α ^ 9 - 1456 * α ^ 10 := by
  have hu : (0 : ℝ) ≤ 6 - α := by linarith
  have h0 : (0:ℝ) ≤ 67214552328 * (6 - α) ^ 10 :=
    mul_nonneg (by norm_num) (pow_nonneg hu 10)
  have h1 : (0:ℝ) ≤ 1324698769152 * α ^ 1 * (6 - α) ^ 9 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 1)) (pow_nonneg hu 9)
  have h2 : (0:ℝ) ≤ 11210565079296 * α ^ 2 * (6 - α) ^ 8 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 2)) (pow_nonneg hu 8)
  have h3 : (0:ℝ) ≤ 51982093082304 * α ^ 3 * (6 - α) ^ 7 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 3)) (pow_nonneg hu 7)
  have h4 : (0:ℝ) ≤ 112831785636336 * α ^ 4 * (6 - α) ^ 6 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 4)) (pow_nonneg hu 6)
  have h5 : (0:ℝ) ≤ 136300060037952 * α ^ 5 * (6 - α) ^ 5 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 5)) (pow_nonneg hu 5)
  have h6 : (0:ℝ) ≤ 172834300408608 * α ^ 6 * (6 - α) ^ 4 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 6)) (pow_nonneg hu 4)
  have h7 : (0:ℝ) ≤ 277236880276032 * α ^ 7 * (6 - α) ^ 3 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 7)) (pow_nonneg hu 3)
  have h8 : (0:ℝ) ≤ 281516219316936 * α ^ 8 * (6 - α) ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 8)) (pow_nonneg hu 2)
  have h9 : (0:ℝ) ≤ 131510134768320 * α ^ 9 * (6 - α) ^ 1 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 9)) (pow_nonneg hu 1)
  have h10 : (0:ℝ) ≤ 19805743188000 * α ^ 10 :=
    mul_nonneg (by norm_num) (pow_nonneg hα 10)
  have hid : (6 : ℝ) ^ 10 * (67214552328 + 108758874312 * α + 64248083658 * α ^ 2 + 8893434528 * α ^ 3 - 26471207052 * α ^ 4 + 9402730740 * α ^ 5 - 77587159 * α ^ 6 - 46242248 * α ^ 7 - 3634800 * α ^ 8 - 118976 * α ^ 9 - 1456 * α ^ 10) = 67214552328 * (6 - α) ^ 10 + 1324698769152 * α ^ 1 * (6 - α) ^ 9 + 11210565079296 * α ^ 2 * (6 - α) ^ 8 + 51982093082304 * α ^ 3 * (6 - α) ^ 7 + 112831785636336 * α ^ 4 * (6 - α) ^ 6 + 136300060037952 * α ^ 5 * (6 - α) ^ 5 + 172834300408608 * α ^ 6 * (6 - α) ^ 4 + 277236880276032 * α ^ 7 * (6 - α) ^ 3 + 281516219316936 * α ^ 8 * (6 - α) ^ 2 + 131510134768320 * α ^ 9 * (6 - α) ^ 1 + 19805743188000 * α ^ 10 := by
    ring
  rcases le_total α (6 / (2 * 1)) with h | h
  · have hpos : (0 : ℝ) < 67214552328 * (6 - α) ^ 10 :=
      mul_pos (by norm_num) (pow_pos (by linarith) 10)
    linarith
  · have hpos : (0 : ℝ) < 19805743188000 * α ^ 10 :=
      mul_pos (by norm_num) (pow_pos (by linarith) 10)
    linarith
end Sendov.B12_13
