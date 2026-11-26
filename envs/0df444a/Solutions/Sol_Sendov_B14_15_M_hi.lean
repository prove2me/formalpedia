-- Prove2me | solution 1 for Sendov.B14_15.M_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:23:09.578907+00:00
-- url     : https://prove2.me/submissions/37e8a897-b539-47ec-9097-d7f89437b938

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree14_15

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B14_15
namespace Sendov.B14_15
theorem _root_.solution : M 15 = 14 := by norm_num [M]
end Sendov.B14_15
