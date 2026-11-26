-- Prove2me | solution 1 for Sendov.B6_6.P_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:20:22.323474+00:00
-- url     : https://prove2.me/submissions/558fcdbc-6304-4427-ae2a-a699ace8788d

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree6_6

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B6_6
set_option maxHeartbeats 2000000
namespace Sendov.B6_6
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 5 / 2) :
    0 < 1575 - 900 * α + 2345 * α ^ 2 - 342 * α ^ 3 - 24 * α ^ 4 := by
  have hu : (0 : ℝ) ≤ 5 - 2 * α := by linarith
  have h0 : (0:ℝ) ≤ 1575 * (5 - 2 * α) ^ 4 :=
    mul_nonneg (by norm_num) (pow_nonneg hu 4)
  have h1 : (0:ℝ) ≤ 8100 * α ^ 1 * (5 - 2 * α) ^ 3 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 1)) (pow_nonneg hu 3)
  have h2 : (0:ℝ) ≤ 69425 * α ^ 2 * (5 - 2 * α) ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 2)) (pow_nonneg hu 2)
  have h3 : (0:ℝ) ≤ 188150 * α ^ 3 * (5 - 2 * α) ^ 1 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 3)) (pow_nonneg hu 1)
  have h4 : (0:ℝ) ≤ 123200 * α ^ 4 :=
    mul_nonneg (by norm_num) (pow_nonneg hα 4)
  have hid : (5 : ℝ) ^ 4 * (1575 - 900 * α + 2345 * α ^ 2 - 342 * α ^ 3 - 24 * α ^ 4) = 1575 * (5 - 2 * α) ^ 4 + 8100 * α ^ 1 * (5 - 2 * α) ^ 3 + 69425 * α ^ 2 * (5 - 2 * α) ^ 2 + 188150 * α ^ 3 * (5 - 2 * α) ^ 1 + 123200 * α ^ 4 := by
    ring
  rcases le_total α (5 / (2 * 2)) with h | h
  · have hpos : (0 : ℝ) < 1575 * (5 - 2 * α) ^ 4 :=
      mul_pos (by norm_num) (pow_pos (by linarith) 4)
    linarith
  · have hpos : (0 : ℝ) < 123200 * α ^ 4 :=
      mul_pos (by norm_num) (pow_pos (by linarith) 4)
    linarith
end Sendov.B6_6
