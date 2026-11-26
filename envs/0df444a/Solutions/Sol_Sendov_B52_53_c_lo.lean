-- Prove2me | solution 1 for Sendov.B52_53.c_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:41:20.946583+00:00
-- url     : https://prove2.me/submissions/86eace47-3a2a-446a-a43f-0c1ccbd3da81

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree52_53
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B52_53
namespace Sendov.B52_53
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) : c 52 α = (306 + 45 * α - 2 * α ^ 2) / (102 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring
end Sendov.B52_53
