-- Prove2me | solution 1 for Sendov.B52_53.M_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:40:53.532258+00:00
-- url     : https://prove2.me/submissions/e4012cdf-2e9f-46d1-b14e-ea4e45215e1c

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree52_53

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B52_53
namespace Sendov.B52_53
theorem _root_.solution : M 52 = 51 := by norm_num [M]
end Sendov.B52_53
