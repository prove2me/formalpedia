-- Prove2me | solution 1 for Sendov.B42_43.c_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:36:38.278805+00:00
-- url     : https://prove2.me/submissions/e4a422d7-d76f-4d8a-b4a7-9ac1e79b0af3

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree42_43
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B42_43
namespace Sendov.B42_43
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) : c 42 α = (246 + 35 * α - 2 * α ^ 2) / (82 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring
end Sendov.B42_43
