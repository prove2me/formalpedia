-- Prove2me | solution 1 for Sendov.B58_60.M_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:45:30.157304+00:00
-- url     : https://prove2.me/submissions/a2671465-54a2-4f9a-b713-01a84f7f827d

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree58_60

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B58_60
namespace Sendov.B58_60
theorem _root_.solution : M 60 = 59 := by norm_num [M]
end Sendov.B58_60
