-- Prove2me | solution 1 for Sendov.B30_31.c_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:30:42.617502+00:00
-- url     : https://prove2.me/submissions/579dcfb8-9136-445c-a450-0998ef9d08b3

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree30_31
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B30_31
namespace Sendov.B30_31
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) : c 30 α = (174 + 23 * α - 2 * α ^ 2) / (58 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring
end Sendov.B30_31
