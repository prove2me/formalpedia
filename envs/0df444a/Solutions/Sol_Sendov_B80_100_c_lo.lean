-- Prove2me | solution 1 for Sendov.B80_100.c_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:00:41.235219+00:00
-- url     : https://prove2.me/submissions/0e4cec31-cce3-4ed2-ba72-1e2616b8016b

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree80_100
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B80_100
namespace Sendov.B80_100
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) : c 80 α = (474 + 73 * α - 2 * α ^ 2) / (158 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring
end Sendov.B80_100
