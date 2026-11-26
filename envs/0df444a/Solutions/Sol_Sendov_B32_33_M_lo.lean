-- Prove2me | solution 1 for Sendov.B32_33.M_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:31:09.928612+00:00
-- url     : https://prove2.me/submissions/3e187c61-340e-4d06-bf48-8f265237a4e9

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree32_33

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B32_33
namespace Sendov.B32_33
theorem _root_.solution : M 32 = 31 := by norm_num [M]
end Sendov.B32_33
