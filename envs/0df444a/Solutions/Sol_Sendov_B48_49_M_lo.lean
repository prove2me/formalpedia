-- Prove2me | solution 1 for Sendov.B48_49.M_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:39:03.266902+00:00
-- url     : https://prove2.me/submissions/6d800e11-e74f-4be0-bddb-8a57738a9f84

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree48_49

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B48_49
namespace Sendov.B48_49
theorem _root_.solution : M 48 = 47 := by norm_num [M]
end Sendov.B48_49
