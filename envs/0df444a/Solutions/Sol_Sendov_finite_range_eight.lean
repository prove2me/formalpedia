-- Prove2me | solution 1 for Sendov.finite_range_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:08:59.819678+00:00
-- url     : https://prove2.me/submissions/05bd7977-1663-4f17-bb34-dcbf7026536b

import Definitions.Def_Sendov_FiniteRange_Reduce
import Definitions.Def_Sendov_FiniteRange_Degree8
import Theorems.Thm_Sendov_M_eight
import Theorems.Thm_Sendov_A_eight
import Theorems.Thm_P2M_Sendov_c_eight__400c24907c3c
import Theorems.Thm_Sendov_R_eight_le
import Theorems.Thm_Sendov_alpha_le_half_M
import Theorems.Thm_Sendov_mom_two
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
open Sendov
open MeasureTheory
variable {α : ℝ}
namespace Sendov
theorem _root_.solution (hα : 0 ≤ α) (hfeas : c 8 α ^ 2 ≤ A 8 α) : R 8 α < 1 := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hle : α ≤ 7 / 2 := by
    have h := alpha_le_half_M (n := 8) (by norm_num) hfeas
    rw [M_eight] at h
    linarith
  have hR := R_eight_le hα
  have hid : 1 / 6 + 1 / (4 * (3 + α)) + 1 / 14 + 1 / (28 * (3 + α))
      + 84 * A 8 α ^ 2 / (3 + α) * mom 8 α 2
      = 1 - (-240 * α ^ 6 - 7488 * α ^ 5 - 60624 * α ^ 4 + 747712 * α ^ 3 - 700161 * α ^ 2
          + 882882 * α + 1102059) / (72030 * (3 + α) ^ 3) := by
    rw [mom_two, A_eight, c_eight' hα]
    field_simp
    ring
  rw [hid] at hR
  have hP : 0 < -240 * α ^ 6 - 7488 * α ^ 5 - 60624 * α ^ 4 + 747712 * α ^ 3 - 700161 * α ^ 2
      + 882882 * α + 1102059 := by
    nlinarith [mul_nonneg (pow_nonneg hα 5) (sub_nonneg.2 hle),
      mul_nonneg (pow_nonneg hα 4) (sub_nonneg.2 hle),
      mul_nonneg (pow_nonneg hα 3) (sub_nonneg.2 hle),
      mul_nonneg hα (sq_nonneg (867020 * α - 700161)), hα, sq_nonneg α]
  have : 0 < (-240 * α ^ 6 - 7488 * α ^ 5 - 60624 * α ^ 4 + 747712 * α ^ 3 - 700161 * α ^ 2
      + 882882 * α + 1102059) / (72030 * (3 + α) ^ 3) := div_pos hP (by positivity)
  linarith
end Sendov
