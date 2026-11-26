-- Prove2me | solution 1 for Sendov.B16_18.A_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:10:23.990994+00:00
-- url     : https://prove2.me/submissions/ab48798d-89ee-47d7-bb2e-c9d2c144e500

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree16_18

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B16_18
namespace Sendov.B16_18
theorem _root_.solution (α : ℝ) : A 16 α = 1 - 2 * α / 15 := by rw [A, M]; push_cast; ring
end Sendov.B16_18
