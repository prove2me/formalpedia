-- Prove2me | solution 1 for Sendov.B16_18.M_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:24:22.8688+00:00
-- url     : https://prove2.me/submissions/362f9391-a60a-4a84-98aa-f43feaaab315

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree16_18

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B16_18
namespace Sendov.B16_18
theorem _root_.solution : M 18 = 17 := by norm_num [M]
end Sendov.B16_18
