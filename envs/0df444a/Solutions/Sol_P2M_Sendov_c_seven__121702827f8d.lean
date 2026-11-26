-- Prove2me | solution 1 for P2M_Sendov_c_seven__121702827f8d
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:17:14.801595+00:00
-- url     : https://prove2.me/submissions/2371670a-71fa-4e74-9bdf-47833adc9d88

import Definitions.Def_Sendov_FiniteRange_Moments
import Definitions.Def_Sendov_FiniteRange_OddBound
import Definitions.Def_Sendov_FiniteRange_Degree7
import Theorems.Thm_Sendov_c_seven
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
open Sendov
open MeasureTheory
variable {α : ℝ}
namespace Sendov
theorem _root_.solution (hα : 0 ≤ α) : c 7 α = (18 - α ^ 2) / (6 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c_seven]
  field_simp
  ring
end Sendov
