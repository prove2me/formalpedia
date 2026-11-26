-- Prove2me | solution 1 for Sendov.B10_11.A_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:09:54.294295+00:00
-- url     : https://prove2.me/submissions/08fbdbdf-89bf-4d38-a013-f8b3cfa63e47

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree10_11

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B10_11
namespace Sendov.B10_11
theorem _root_.solution (α : ℝ) : A 10 α = 1 - 2 * α / 9 := by rw [A, M]; push_cast; ring
end Sendov.B10_11
