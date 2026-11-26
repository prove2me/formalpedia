-- Prove2me | solution 1 for Sendov.B44_45.c_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:37:58.290249+00:00
-- url     : https://prove2.me/submissions/d94c28ec-3aa4-4299-90b1-e0e0a918ac99

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree44_45
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B44_45
namespace Sendov.B44_45
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) : c 44 α = (258 + 37 * α - 2 * α ^ 2) / (86 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring
end Sendov.B44_45
