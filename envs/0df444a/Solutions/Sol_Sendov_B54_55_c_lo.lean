-- Prove2me | solution 1 for Sendov.B54_55.c_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:43:10.558869+00:00
-- url     : https://prove2.me/submissions/e94d0826-ab21-4928-80a9-2292f4136c38

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree54_55
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B54_55
namespace Sendov.B54_55
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) : c 54 α = (318 + 47 * α - 2 * α ^ 2) / (106 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring
end Sendov.B54_55
