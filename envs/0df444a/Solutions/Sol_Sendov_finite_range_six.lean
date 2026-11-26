-- Prove2me | solution 1 for Sendov.finite_range_six
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:08:49.269024+00:00
-- url     : https://prove2.me/submissions/fdfc4e74-4459-4c27-86b8-6e4c251b7bb4

import Definitions.Def_Sendov_Common_Basic
import Definitions.Def_Sendov_FiniteRange_Moments
import Definitions.Def_Sendov_FiniteRange_Degree6
import Theorems.Thm_Sendov_M_six
import Theorems.Thm_Sendov_one_sub_R_six
import Theorems.Thm_Sendov_alpha_le_half_M


set_option autoImplicit false
open Sendov
open MeasureTheory
variable {α : ℝ}
namespace Sendov
theorem _root_.solution (hα : 0 ≤ α) (hfeas : c 6 α ^ 2 ≤ A 6 α) : R 6 α < 1 := by
  have hle : α ≤ 3 := by
    have h := alpha_le_half_M (n := 6) (by norm_num) hfeas
    rw [M_six] at h
    linarith
  have hP : 0 < -24 * α ^ 4 - 342 * α ^ 3 + 2345 * α ^ 2 - 900 * α + 1575 := by
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hα hα) hα) (sub_nonneg.2 hle),
      mul_nonneg (mul_nonneg hα hα) (sub_nonneg.2 hle), sq_nonneg (1103 * α - 450)]
  have hpos : 0 < 1 - R 6 α := by
    rw [one_sub_R_six hα]
    exact div_pos hP (by positivity)
  linarith
end Sendov
