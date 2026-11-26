-- Prove2me | solution 1 for Sendov.B34_35.c_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:33:08.713439+00:00
-- url     : https://prove2.me/submissions/16a9ce28-17ca-4535-bf1e-6561dfad95e8

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree34_35
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B34_35
namespace Sendov.B34_35
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) : c 34 α = (198 + 27 * α - 2 * α ^ 2) / (66 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring
end Sendov.B34_35
