-- Prove2me | solution 1 for Sendov.B46_47.A_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:38:36.291678+00:00
-- url     : https://prove2.me/submissions/5b9abd97-3a6f-49a2-9768-7b3db82c06f9

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree46_47

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B46_47
namespace Sendov.B46_47
theorem _root_.solution (α : ℝ) : A 47 α = 1 - 2 * α / 46 := by rw [A, M]; push_cast; ring
end Sendov.B46_47
