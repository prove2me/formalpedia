-- Prove2me | solution 1 for Sendov.B32_33.c_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:32:04.790841+00:00
-- url     : https://prove2.me/submissions/0025fd9a-b83a-4bbe-827e-2e743169791a

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree32_33
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B32_33
namespace Sendov.B32_33
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) : c 32 α = (186 + 25 * α - 2 * α ^ 2) / (62 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring
end Sendov.B32_33
