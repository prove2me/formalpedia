-- Prove2me | solution 1 for Sendov.B48_49.c_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:39:28.280399+00:00
-- url     : https://prove2.me/submissions/e4baf3de-4b75-49b5-9ea9-a4a8375c1e43

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree48_49
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B48_49
namespace Sendov.B48_49
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) : c 48 α = (282 + 41 * α - 2 * α ^ 2) / (94 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring
end Sendov.B48_49
