-- Prove2me | solution 1 for P2M_Sendov_c_six__13488b48dfc2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:08:29.41298+00:00
-- url     : https://prove2.me/submissions/95d26027-981e-4326-af07-47360b6ec1cf

import Definitions.Def_Sendov_Common_Basic
import Definitions.Def_Sendov_FiniteRange_Moments
import Definitions.Def_Sendov_FiniteRange_Degree6
import Theorems.Thm_Sendov_c_six
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
open Sendov
open MeasureTheory
variable {α : ℝ}
namespace Sendov
theorem _root_.solution (hα : 0 ≤ α) : c 6 α = (30 - α - 2 * α ^ 2) / (10 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c_six]
  field_simp
  ring
end Sendov
