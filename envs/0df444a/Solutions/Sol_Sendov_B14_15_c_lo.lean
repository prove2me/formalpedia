-- Prove2me | solution 1 for Sendov.B14_15.c_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:23:25.088613+00:00
-- url     : https://prove2.me/submissions/254aab21-cab2-4d5d-b7e3-26a1a9652744

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree14_15
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B14_15
namespace Sendov.B14_15
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) : c 14 α = (78 + 7 * α - 2 * α ^ 2) / (26 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring
end Sendov.B14_15
