-- Prove2me | solution 1 for Sendov.B14_15.A_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:10:21.584648+00:00
-- url     : https://prove2.me/submissions/de0a9c47-c0e3-41ba-83ff-fc8c3e3c1427

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree14_15

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B14_15
namespace Sendov.B14_15
theorem _root_.solution (α : ℝ) : A 14 α = 1 - 2 * α / 13 := by rw [A, M]; push_cast; ring
end Sendov.B14_15
