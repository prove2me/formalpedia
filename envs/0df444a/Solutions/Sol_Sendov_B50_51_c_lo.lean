-- Prove2me | solution 1 for Sendov.B50_51.c_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:40:21.710483+00:00
-- url     : https://prove2.me/submissions/68a754da-8c4e-48b9-bb4e-0c47c69699a4

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree50_51
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B50_51
namespace Sendov.B50_51
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) : c 50 α = (294 + 43 * α - 2 * α ^ 2) / (98 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring
end Sendov.B50_51
