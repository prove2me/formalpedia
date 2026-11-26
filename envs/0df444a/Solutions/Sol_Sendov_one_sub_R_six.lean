-- Prove2me | solution 1 for Sendov.one_sub_R_six
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:16:28.887411+00:00
-- url     : https://prove2.me/submissions/e684114a-8c31-4970-badb-b102fa630478

import Definitions.Def_Sendov_Common_Basic
import Definitions.Def_Sendov_FiniteRange_Moments
import Definitions.Def_Sendov_FiniteRange_Degree6
import Theorems.Thm_Sendov_M_six
import Theorems.Thm_Sendov_A_six
import Theorems.Thm_Sendov_c_six
import Theorems.Thm_Sendov_integral_six
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
open Sendov
open MeasureTheory
variable {α : ℝ}
namespace Sendov
theorem _root_.solution (hα : 0 ≤ α) :
    1 - R 6 α
      = (-24 * α ^ 4 - 342 * α ^ 3 + 2345 * α ^ 2 - 900 * α + 1575) / (375 * (3 + α) ^ 2) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [R, integral_six, A_six, c_six, M_six]
  push_cast
  field_simp
  ring
end Sendov
