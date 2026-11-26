-- Prove2me | solution 1 for Sendov.B40_41.c_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:35:55.170862+00:00
-- url     : https://prove2.me/submissions/e1b3f9b3-ac6e-4dcd-a07e-736eed9d5750

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree40_41
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B40_41
namespace Sendov.B40_41
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) : c 40 α = (234 + 33 * α - 2 * α ^ 2) / (78 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring
end Sendov.B40_41
