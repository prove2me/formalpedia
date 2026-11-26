-- Prove2me | solution 1 for Sendov.B22_24.M_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:27:02.522868+00:00
-- url     : https://prove2.me/submissions/ca599f15-f6ea-4bfa-ac0f-9497d25f0276

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree22_24

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B22_24
namespace Sendov.B22_24
theorem _root_.solution : M 24 = 23 := by norm_num [M]
end Sendov.B22_24
