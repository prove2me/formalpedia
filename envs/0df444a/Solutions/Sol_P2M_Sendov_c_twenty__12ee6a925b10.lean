-- Prove2me | solution 1 for P2M_Sendov_c_twenty__12ee6a925b10
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:19:17.896309+00:00
-- url     : https://prove2.me/submissions/8decc180-fe5a-41dd-a3c9-3bd5a032d6f3

import Definitions.Def_Sendov_FiniteRange_Reduce
import Definitions.Def_Sendov_FiniteRange_Degree20
import Theorems.Thm_Sendov_c_twenty
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option maxRecDepth 8000
open Sendov
open MeasureTheory
variable {α : ℝ}
namespace Sendov
theorem _root_.solution (hα : 0 ≤ α) : c 20 α = (114 + 13 * α - 2 * α ^ 2) / (38 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c_twenty]
  field_simp
  ring
end Sendov
