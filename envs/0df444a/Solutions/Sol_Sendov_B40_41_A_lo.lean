-- Prove2me | solution 1 for Sendov.B40_41.A_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:12:33.19614+00:00
-- url     : https://prove2.me/submissions/a04854df-4ed8-48d3-b06e-0af124c03dfe

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree40_41

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B40_41
namespace Sendov.B40_41
theorem _root_.solution (α : ℝ) : A 40 α = 1 - 2 * α / 39 := by rw [A, M]; push_cast; ring
end Sendov.B40_41
