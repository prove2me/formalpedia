-- Prove2me | solution 1 for Sendov.B8_9.c_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:21:14.6874+00:00
-- url     : https://prove2.me/submissions/8c3f57ac-f161-42f6-a940-a169d0cbdc9b

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree8_9
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B8_9
namespace Sendov.B8_9
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) : c 8 α = (42 + 1 * α - 2 * α ^ 2) / (14 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring
end Sendov.B8_9
