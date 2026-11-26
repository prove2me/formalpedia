-- Prove2me | solution 1 for Sendov.B60_63.c_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:47:00.886684+00:00
-- url     : https://prove2.me/submissions/a12303f5-b8de-4ef4-b16e-7194b6058f4a

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree60_63
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B60_63
namespace Sendov.B60_63
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) : c 60 α = (354 + 53 * α - 2 * α ^ 2) / (118 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring
end Sendov.B60_63
