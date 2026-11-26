-- Prove2me | solution 1 for Sendov.B34_35.M_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:32:58.760797+00:00
-- url     : https://prove2.me/submissions/f3b505a4-a877-415d-96ea-a2feaa665e3a

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree34_35

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B34_35
namespace Sendov.B34_35
theorem _root_.solution : M 35 = 34 := by norm_num [M]
end Sendov.B34_35
