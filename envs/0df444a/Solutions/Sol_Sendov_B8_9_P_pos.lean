-- Prove2me | solution 1 for Sendov.B8_9.P_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:21:17.284694+00:00
-- url     : https://prove2.me/submissions/0010f225-aa15-4666-83c5-13c0f4d1495f

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree8_9

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B8_9
set_option maxHeartbeats 2000000
namespace Sendov.B8_9
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 4) :
    0 < 656208 + 407736 * α - 877827 * α ^ 2 + 621074 * α ^ 3 - 39267 * α ^ 4 - 5436 * α ^ 5 - 180 * α ^ 6 := by
  have hu : (0 : ℝ) ≤ 4 - α := by linarith
  have h0 : (0:ℝ) ≤ 656208 * (4 - α) ^ 6 :=
    mul_nonneg (by norm_num) (pow_nonneg hu 6)
  have h1 : (0:ℝ) ≤ 5568192 * α ^ 1 * (4 - α) ^ 5 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 1)) (pow_nonneg hu 5)
  have h2 : (0:ℝ) ≤ 3952608 * α ^ 2 * (4 - α) ^ 4 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 2)) (pow_nonneg hu 4)
  have h3 : (0:ℝ) ≤ 13001408 * α ^ 3 * (4 - α) ^ 3 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 3)) (pow_nonneg hu 3)
  have h4 : (0:ℝ) ≤ 51075024 * α ^ 4 * (4 - α) ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 4)) (pow_nonneg hu 2)
  have h5 : (0:ℝ) ≤ 49486080 * α ^ 5 * (4 - α) ^ 1 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 5)) (pow_nonneg hu 1)
  have h6 : (0:ℝ) ≤ 11634560 * α ^ 6 :=
    mul_nonneg (by norm_num) (pow_nonneg hα 6)
  have hid : (4 : ℝ) ^ 6 * (656208 + 407736 * α - 877827 * α ^ 2 + 621074 * α ^ 3 - 39267 * α ^ 4 - 5436 * α ^ 5 - 180 * α ^ 6) = 656208 * (4 - α) ^ 6 + 5568192 * α ^ 1 * (4 - α) ^ 5 + 3952608 * α ^ 2 * (4 - α) ^ 4 + 13001408 * α ^ 3 * (4 - α) ^ 3 + 51075024 * α ^ 4 * (4 - α) ^ 2 + 49486080 * α ^ 5 * (4 - α) ^ 1 + 11634560 * α ^ 6 := by
    ring
  rcases le_total α (4 / (2 * 1)) with h | h
  · have hpos : (0 : ℝ) < 656208 * (4 - α) ^ 6 :=
      mul_pos (by norm_num) (pow_pos (by linarith) 6)
    linarith
  · have hpos : (0 : ℝ) < 11634560 * α ^ 6 :=
      mul_pos (by norm_num) (pow_pos (by linarith) 6)
    linarith
end Sendov.B8_9
