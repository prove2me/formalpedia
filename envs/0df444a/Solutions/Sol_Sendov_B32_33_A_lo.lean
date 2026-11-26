-- Prove2me | solution 1 for Sendov.B32_33.A_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:11:44.361934+00:00
-- url     : https://prove2.me/submissions/0919a757-f306-4df4-82e4-430d0d331cb5

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree32_33

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B32_33
namespace Sendov.B32_33
theorem _root_.solution (α : ℝ) : A 32 α = 1 - 2 * α / 31 := by rw [A, M]; push_cast; ring
end Sendov.B32_33
