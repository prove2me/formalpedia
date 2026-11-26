-- Prove2me | solution 1 for Sendov.B64_69.c_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:48:41.574396+00:00
-- url     : https://prove2.me/submissions/67b44e3d-4e15-47ec-976e-00363d4e9ab2

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree64_69
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B64_69
namespace Sendov.B64_69
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) : c 64 α = (378 + 57 * α - 2 * α ^ 2) / (126 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring
end Sendov.B64_69
