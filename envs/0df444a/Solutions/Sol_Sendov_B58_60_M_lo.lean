-- Prove2me | solution 1 for Sendov.B58_60.M_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:45:19.836932+00:00
-- url     : https://prove2.me/submissions/2fba12c4-31e1-43ca-adc2-0fbfb824ee77

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree58_60

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B58_60
namespace Sendov.B58_60
theorem _root_.solution : M 58 = 57 := by norm_num [M]
end Sendov.B58_60
