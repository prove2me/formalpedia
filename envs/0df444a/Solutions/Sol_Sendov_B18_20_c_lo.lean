-- Prove2me | solution 1 for Sendov.B18_20.c_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:25:14.705143+00:00
-- url     : https://prove2.me/submissions/2c257cc7-355f-412a-bf19-cabb413c45fc

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree18_20
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B18_20
namespace Sendov.B18_20
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) : c 18 α = (102 + 11 * α - 2 * α ^ 2) / (34 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring
end Sendov.B18_20
