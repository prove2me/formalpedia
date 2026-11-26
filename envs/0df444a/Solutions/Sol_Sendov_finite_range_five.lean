-- Prove2me | solution 1 for Sendov.finite_range_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:08:26.464534+00:00
-- url     : https://prove2.me/submissions/a9cfb8a3-ad81-450b-90c9-c62a8bbe10f8

import Definitions.Def_Sendov_FiniteRange_Moments
import Definitions.Def_Sendov_FiniteRange_OddBound
import Definitions.Def_Sendov_FiniteRange_Degree5
import Theorems.Thm_Sendov_M_five
import Theorems.Thm_Sendov_A_five
import Theorems.Thm_P2M_Sendov_c_five__664be7217b50
import Theorems.Thm_Sendov_R_five_le
import Theorems.Thm_Sendov_alpha_le_half_M
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
open Sendov
open MeasureTheory
variable {α : ℝ}
namespace Sendov
theorem _root_.solution (hα : 0 ≤ α) (hfeas : c 5 α ^ 2 ≤ A 5 α) : R 5 α < 1 := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hle : α ≤ 2 := by
    have h := alpha_le_half_M (n := 5) (by norm_num) hfeas
    rw [M_five] at h
    linarith
  have hR := R_five_le hα hfeas
  have hid : 1 / 6 + 1 / (4 * (3 + α)) + 1 / 8 + 1 / (16 * (3 + α))
      + 60 * A 5 α ^ 2 / (4 * (3 + α))
        * (3 / 2 * (1 / 4 - 2 * c 5 α / 5 + A 5 α / 6) + 1 / 24)
      = 1 - (-9 * α ^ 4 - 123 * α ^ 3 + 596 * α ^ 2 + 30 * α + 234) / (96 * (3 + α) ^ 2) := by
    rw [A_five, c_five' hα]
    field_simp
    ring
  rw [hid] at hR
  have hP : 0 < -9 * α ^ 4 - 123 * α ^ 3 + 596 * α ^ 2 + 30 * α + 234 := by
    nlinarith [mul_nonneg (pow_nonneg hα 3) (sub_nonneg.2 hle),
      mul_nonneg (pow_nonneg hα 2) (sub_nonneg.2 hle), sq_nonneg α, hα]
  have : 0 < (-9 * α ^ 4 - 123 * α ^ 3 + 596 * α ^ 2 + 30 * α + 234) / (96 * (3 + α) ^ 2) :=
    div_pos hP (by positivity)
  linarith
end Sendov
