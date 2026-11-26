-- Prove2me | solution 1 for Sendov.B58_60.c_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:45:57.211037+00:00
-- url     : https://prove2.me/submissions/eaecd4bc-782c-43e8-9054-9e0fd90e901c

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree58_60
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B58_60
namespace Sendov.B58_60
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) : c 58 α = (342 + 51 * α - 2 * α ^ 2) / (114 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring
end Sendov.B58_60
