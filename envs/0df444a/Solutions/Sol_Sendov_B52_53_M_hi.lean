-- Prove2me | solution 1 for Sendov.B52_53.M_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:41:00.0471+00:00
-- url     : https://prove2.me/submissions/b157b204-370b-41e2-8194-3684ef5a8a5e

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree52_53

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B52_53
namespace Sendov.B52_53
theorem _root_.solution : M 53 = 52 := by norm_num [M]
end Sendov.B52_53
