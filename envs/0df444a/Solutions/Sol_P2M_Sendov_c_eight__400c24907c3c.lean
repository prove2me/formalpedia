-- Prove2me | solution 1 for P2M_Sendov_c_eight__400c24907c3c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:18:00.827322+00:00
-- url     : https://prove2.me/submissions/0999e6f9-74e7-4c2f-b969-f8ca865881ab

import Definitions.Def_Sendov_FiniteRange_Reduce
import Definitions.Def_Sendov_FiniteRange_Degree8
import Theorems.Thm_Sendov_c_eight
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
open Sendov
open MeasureTheory
variable {α : ℝ}
namespace Sendov
theorem _root_.solution (hα : 0 ≤ α) : c 8 α = (42 + α - 2 * α ^ 2) / (14 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c_eight]
  field_simp
  ring
end Sendov
