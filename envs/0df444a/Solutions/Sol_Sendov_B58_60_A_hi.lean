-- Prove2me | solution 1 for Sendov.B58_60.A_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:45:37.36381+00:00
-- url     : https://prove2.me/submissions/897adb65-cca0-4c82-99e1-14369e200b29

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree58_60

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B58_60
namespace Sendov.B58_60
theorem _root_.solution (α : ℝ) : A 60 α = 1 - 2 * α / 59 := by rw [A, M]; push_cast; ring
end Sendov.B58_60
