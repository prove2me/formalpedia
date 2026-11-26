-- Prove2me | solution 1 for Sendov.B24_26.c_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:28:18.861966+00:00
-- url     : https://prove2.me/submissions/85f3b1a9-4b4d-44ad-9812-ee2c7dff9dde

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree24_26
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B24_26
namespace Sendov.B24_26
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) : c 24 α = (138 + 17 * α - 2 * α ^ 2) / (46 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring
end Sendov.B24_26
