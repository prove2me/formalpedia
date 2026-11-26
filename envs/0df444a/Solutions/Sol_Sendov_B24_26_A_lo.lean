-- Prove2me | solution 1 for Sendov.B24_26.A_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:11:08.900459+00:00
-- url     : https://prove2.me/submissions/485dff60-7d49-492d-8e2b-3b3f6d7e70fb

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree24_26

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B24_26
namespace Sendov.B24_26
theorem _root_.solution (α : ℝ) : A 24 α = 1 - 2 * α / 23 := by rw [A, M]; push_cast; ring
end Sendov.B24_26
