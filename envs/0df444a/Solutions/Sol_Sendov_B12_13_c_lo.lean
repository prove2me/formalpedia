-- Prove2me | solution 1 for Sendov.B12_13.c_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:22:57.085135+00:00
-- url     : https://prove2.me/submissions/8f9972dd-8d86-467d-91d6-c71c26799224

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree12_13
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B12_13
namespace Sendov.B12_13
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) : c 12 α = (66 + 5 * α - 2 * α ^ 2) / (22 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring
end Sendov.B12_13
