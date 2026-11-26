-- Prove2me | solution 1 for Sendov.B6_6.c_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:20:20.203375+00:00
-- url     : https://prove2.me/submissions/a7f6e0ba-456c-4ed5-9cf7-22beb0c4a5aa

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree6_6
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B6_6
namespace Sendov.B6_6
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) : c 6 α = (30 - 1 * α - 2 * α ^ 2) / (10 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring
end Sendov.B6_6
