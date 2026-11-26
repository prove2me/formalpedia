-- Prove2me | solution 1 for Sendov.B22_24.c_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:27:43.479335+00:00
-- url     : https://prove2.me/submissions/fde09503-1963-42a4-bc88-d03ffa61420e

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree22_24
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B22_24
namespace Sendov.B22_24
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) : c 22 α = (126 + 15 * α - 2 * α ^ 2) / (42 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring
end Sendov.B22_24
