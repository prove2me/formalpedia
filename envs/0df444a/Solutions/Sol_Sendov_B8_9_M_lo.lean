-- Prove2me | solution 1 for Sendov.B8_9.M_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:20:33.05501+00:00
-- url     : https://prove2.me/submissions/7d183549-7e20-459f-9b9c-0ac0fc7b03f4

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree8_9

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B8_9
namespace Sendov.B8_9
theorem _root_.solution : M 8 = 7 := by norm_num [M]
end Sendov.B8_9
