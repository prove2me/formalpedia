-- Prove2me | solution 1 for Sendov.B10_11.M_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:21:25.92021+00:00
-- url     : https://prove2.me/submissions/629a8c78-89e3-4656-bc82-b47f12f214a5

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree10_11

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B10_11
namespace Sendov.B10_11
theorem _root_.solution : M 11 = 10 := by norm_num [M]
end Sendov.B10_11
