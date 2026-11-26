-- Prove2me | solution 1 for Sendov.B16_18.c_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:24:31.870704+00:00
-- url     : https://prove2.me/submissions/7b0df255-2f8a-477d-bf84-82d9649164bd

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree16_18
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B16_18
namespace Sendov.B16_18
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) : c 16 α = (90 + 9 * α - 2 * α ^ 2) / (30 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring
end Sendov.B16_18
