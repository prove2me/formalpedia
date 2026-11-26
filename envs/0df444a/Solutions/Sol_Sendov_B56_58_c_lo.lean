-- Prove2me | solution 1 for Sendov.B56_58.c_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:44:09.439537+00:00
-- url     : https://prove2.me/submissions/5c8240a6-82de-4441-9978-5f737412b1c3

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree56_58
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B56_58
namespace Sendov.B56_58
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) : c 56 α = (330 + 49 * α - 2 * α ^ 2) / (110 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring
end Sendov.B56_58
