-- Prove2me | solution 1 for Sendov.B6_6.M_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:09:28.456798+00:00
-- url     : https://prove2.me/submissions/7de233cc-1764-4baa-baa2-33859ba1b05a

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree6_6

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B6_6
namespace Sendov.B6_6
theorem _root_.solution : M 6 = 5 := by norm_num [M]
end Sendov.B6_6
