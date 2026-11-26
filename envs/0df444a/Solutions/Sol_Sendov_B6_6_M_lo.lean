-- Prove2me | solution 1 for Sendov.B6_6.M_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:19:18.991167+00:00
-- url     : https://prove2.me/submissions/98af0833-51e9-4b03-9246-7e76a80bb04e

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
