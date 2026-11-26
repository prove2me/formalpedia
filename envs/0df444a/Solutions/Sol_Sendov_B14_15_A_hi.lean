-- Prove2me | solution 1 for Sendov.B14_15.A_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:23:10.803917+00:00
-- url     : https://prove2.me/submissions/293db6a6-39d3-4de7-afb3-f1d40cb7a2a6

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree14_15

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B14_15
namespace Sendov.B14_15
theorem _root_.solution (α : ℝ) : A 15 α = 1 - 2 * α / 14 := by rw [A, M]; push_cast; ring
end Sendov.B14_15
