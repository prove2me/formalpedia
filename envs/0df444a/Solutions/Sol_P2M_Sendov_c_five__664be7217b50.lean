-- Prove2me | solution 1 for P2M_Sendov_c_five__664be7217b50
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:15:24.911816+00:00
-- url     : https://prove2.me/submissions/0c192d59-6dcc-44d5-a269-d44a6bf9eb7d

import Definitions.Def_Sendov_FiniteRange_Moments
import Definitions.Def_Sendov_FiniteRange_OddBound
import Definitions.Def_Sendov_FiniteRange_Degree5
import Theorems.Thm_Sendov_c_five
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
open Sendov
open MeasureTheory
variable {α : ℝ}
namespace Sendov
theorem _root_.solution (hα : 0 ≤ α) : c 5 α = (12 - α - α ^ 2) / (4 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c_five]
  field_simp
  ring
end Sendov
