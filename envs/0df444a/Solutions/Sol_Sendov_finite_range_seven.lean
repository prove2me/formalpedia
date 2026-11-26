-- Prove2me | solution 1 for Sendov.finite_range_seven
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:08:53.354458+00:00
-- url     : https://prove2.me/submissions/adc2697e-a652-4682-9e02-ef82156f7f15

import Definitions.Def_Sendov_FiniteRange_Moments
import Definitions.Def_Sendov_FiniteRange_OddBound
import Definitions.Def_Sendov_FiniteRange_Degree7
import Theorems.Thm_Sendov_M_seven
import Theorems.Thm_Sendov_A_seven
import Theorems.Thm_P2M_Sendov_c_seven__121702827f8d
import Theorems.Thm_Sendov_R_seven_le
import Theorems.Thm_Sendov_alpha_le_half_M
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
open Sendov
open MeasureTheory
variable {α : ℝ}
namespace Sendov
theorem _root_.solution (hα : 0 ≤ α) (hfeas : c 7 α ^ 2 ≤ A 7 α) : R 7 α < 1 := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hle : α ≤ 3 := by
    have h := alpha_le_half_M (n := 7) (by norm_num) hfeas
    rw [M_seven] at h
    linarith
  have hR := R_seven_le hα hfeas
  have hid : 1 / 6 + 1 / (4 * (3 + α)) + 1 / 12 + 1 / (24 * (3 + α))
      + 210 * A 7 α ^ 2 / (4 * (3 + α))
        * (1 / 4 - 3 * c 7 α / 5 + (4 * c 7 α ^ 2 + 3 * A 7 α) / 12
          - 2 * c 7 α * A 7 α / 7 + A 7 α ^ 2 / 16)
      = 1 - (-5 * α ^ 6 - 222 * α ^ 5 - 2619 * α ^ 4 + 17388 * α ^ 3 + 19413 * α ^ 2
          - 5022 * α + 33291) / (2592 * (3 + α) ^ 3) := by
    rw [A_seven, c_seven' hα]
    field_simp
    ring
  rw [hid] at hR
  have hP : 0 < -5 * α ^ 6 - 222 * α ^ 5 - 2619 * α ^ 4 + 17388 * α ^ 3 + 19413 * α ^ 2
      - 5022 * α + 33291 := by
    nlinarith [mul_nonneg (pow_nonneg hα 3) (sub_nonneg.2 hle),
      mul_nonneg (pow_nonneg hα 4) (sub_nonneg.2 hle),
      mul_nonneg (pow_nonneg hα 5) (sub_nonneg.2 hle),
      sq_nonneg (19413 * α - 2511)]
  have : 0 < (-5 * α ^ 6 - 222 * α ^ 5 - 2619 * α ^ 4 + 17388 * α ^ 3 + 19413 * α ^ 2
      - 5022 * α + 33291) / (2592 * (3 + α) ^ 3) := div_pos hP (by positivity)
  linarith
end Sendov
