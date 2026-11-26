-- Prove2me | solution 1 for Sendov.B60_63.M_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:46:37.295402+00:00
-- url     : https://prove2.me/submissions/6eb5ca89-2acc-43d4-aa9d-f2f3e3eab050

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree60_63

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B60_63
namespace Sendov.B60_63
theorem _root_.solution : M 60 = 59 := by norm_num [M]
end Sendov.B60_63
