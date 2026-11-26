-- Prove2me | solution 1 for Sendov.B22_24.M_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:27:01.747942+00:00
-- url     : https://prove2.me/submissions/a923d988-2efa-422e-9876-c70ab303897b

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree22_24

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B22_24
namespace Sendov.B22_24
theorem _root_.solution : M 22 = 21 := by norm_num [M]
end Sendov.B22_24
