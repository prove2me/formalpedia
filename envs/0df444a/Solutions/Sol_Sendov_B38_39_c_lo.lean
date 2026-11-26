-- Prove2me | solution 1 for Sendov.B38_39.c_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:34:47.025817+00:00
-- url     : https://prove2.me/submissions/5a497006-9670-47a7-8756-4b10437d15ed

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree38_39
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B38_39
namespace Sendov.B38_39
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) : c 38 α = (222 + 31 * α - 2 * α ^ 2) / (74 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring
end Sendov.B38_39
