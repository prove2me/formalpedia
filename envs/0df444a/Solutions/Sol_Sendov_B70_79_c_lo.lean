-- Prove2me | solution 1 for Sendov.B70_79.c_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:50:40.721804+00:00
-- url     : https://prove2.me/submissions/f6977537-ff72-4ff9-970f-c3c778327f3b

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree70_79
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B70_79
namespace Sendov.B70_79
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) : c 70 α = (414 + 63 * α - 2 * α ^ 2) / (138 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring
end Sendov.B70_79
