-- Prove2me | solution 1 for Sendov.B32_33.A_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:32:03.989104+00:00
-- url     : https://prove2.me/submissions/0981a2f0-c53c-4e09-a13a-711a13127107

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree32_33

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B32_33
namespace Sendov.B32_33
theorem _root_.solution (α : ℝ) : A 33 α = 1 - 2 * α / 32 := by rw [A, M]; push_cast; ring
end Sendov.B32_33
