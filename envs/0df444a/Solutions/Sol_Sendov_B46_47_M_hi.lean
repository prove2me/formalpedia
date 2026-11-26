-- Prove2me | solution 1 for Sendov.B46_47.M_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:38:28.190597+00:00
-- url     : https://prove2.me/submissions/92509643-0fc0-496b-88e0-4ad55e97d193

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree46_47

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B46_47
namespace Sendov.B46_47
theorem _root_.solution : M 47 = 46 := by norm_num [M]
end Sendov.B46_47
