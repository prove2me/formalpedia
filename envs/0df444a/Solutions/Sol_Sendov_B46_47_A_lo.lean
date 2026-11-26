-- Prove2me | solution 1 for Sendov.B46_47.A_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:13:10.118676+00:00
-- url     : https://prove2.me/submissions/3b5f6183-7433-4c65-ac65-ec4b8381d207

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree46_47

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B46_47
namespace Sendov.B46_47
theorem _root_.solution (α : ℝ) : A 46 α = 1 - 2 * α / 45 := by rw [A, M]; push_cast; ring
end Sendov.B46_47
