-- Prove2me | solution 1 for Sendov.B46_47.c_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:38:37.473801+00:00
-- url     : https://prove2.me/submissions/3ea2b5da-ee5b-4c6d-91ac-1a7afc196aef

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree46_47
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B46_47
namespace Sendov.B46_47
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) : c 46 α = (270 + 39 * α - 2 * α ^ 2) / (90 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring
end Sendov.B46_47
