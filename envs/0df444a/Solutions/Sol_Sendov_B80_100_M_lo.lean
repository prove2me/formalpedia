-- Prove2me | solution 1 for Sendov.B80_100.M_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:00:40.60129+00:00
-- url     : https://prove2.me/submissions/69722bb8-6dec-407a-b7bc-a7495f86e98c

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree80_100

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B80_100
namespace Sendov.B80_100
theorem _root_.solution : M 80 = 79 := by norm_num [M]
end Sendov.B80_100
