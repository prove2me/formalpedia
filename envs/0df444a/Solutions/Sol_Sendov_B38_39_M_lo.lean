-- Prove2me | solution 1 for Sendov.B38_39.M_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:34:12.523073+00:00
-- url     : https://prove2.me/submissions/0e2494e3-1c26-4469-bfcd-1b08dc9836a8

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree38_39

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B38_39
namespace Sendov.B38_39
theorem _root_.solution : M 38 = 37 := by norm_num [M]
end Sendov.B38_39
