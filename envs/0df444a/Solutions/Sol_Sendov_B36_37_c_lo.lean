-- Prove2me | solution 1 for Sendov.B36_37.c_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:33:58.639487+00:00
-- url     : https://prove2.me/submissions/15e30545-d020-4f68-a225-14df5b7d64c9

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree36_37
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B36_37
namespace Sendov.B36_37
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) : c 36 α = (210 + 29 * α - 2 * α ^ 2) / (70 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring
end Sendov.B36_37
