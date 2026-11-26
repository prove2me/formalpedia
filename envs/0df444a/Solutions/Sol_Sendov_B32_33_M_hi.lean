-- Prove2me | solution 1 for Sendov.B32_33.M_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:31:10.522799+00:00
-- url     : https://prove2.me/submissions/138308f7-a864-4499-b4b8-6d342850365f

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree32_33

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B32_33
namespace Sendov.B32_33
theorem _root_.solution : M 33 = 32 := by norm_num [M]
end Sendov.B32_33
