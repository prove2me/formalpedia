-- Prove2me | solution 1 for Sendov.B46_47.M_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:38:13.307997+00:00
-- url     : https://prove2.me/submissions/ae15a7a0-5632-4ef5-9f88-823c7d89b456

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree46_47

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B46_47
namespace Sendov.B46_47
theorem _root_.solution : M 46 = 45 := by norm_num [M]
end Sendov.B46_47
