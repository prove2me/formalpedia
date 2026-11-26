-- Prove2me | solution 1 for Sendov.B40_41.M_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:35:44.311361+00:00
-- url     : https://prove2.me/submissions/327de4bd-6c1d-4b77-bb94-3eec4b4882cc

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree40_41

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B40_41
namespace Sendov.B40_41
theorem _root_.solution : M 41 = 40 := by norm_num [M]
end Sendov.B40_41
