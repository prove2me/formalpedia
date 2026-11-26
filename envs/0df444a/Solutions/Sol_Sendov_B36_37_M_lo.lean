-- Prove2me | solution 1 for Sendov.B36_37.M_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:33:29.391551+00:00
-- url     : https://prove2.me/submissions/1914a119-c1c5-40d4-96b6-6f5332ebe9cf

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree36_37

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B36_37
namespace Sendov.B36_37
theorem _root_.solution : M 36 = 35 := by norm_num [M]
end Sendov.B36_37
