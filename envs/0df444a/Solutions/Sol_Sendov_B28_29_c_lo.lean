-- Prove2me | solution 1 for Sendov.B28_29.c_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:29:40.206843+00:00
-- url     : https://prove2.me/submissions/b43e0e6c-99c6-4159-aadb-2a5f571b406e

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree28_29
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B28_29
namespace Sendov.B28_29
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) : c 28 α = (162 + 21 * α - 2 * α ^ 2) / (54 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring
end Sendov.B28_29
