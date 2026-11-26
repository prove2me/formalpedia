-- Prove2me | solution 1 for Sendov.B60_63.M_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:46:39.789939+00:00
-- url     : https://prove2.me/submissions/f8aa3f94-e478-4f5b-8daa-92eaa6a49a2d

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree60_63

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B60_63
namespace Sendov.B60_63
theorem _root_.solution : M 63 = 62 := by norm_num [M]
end Sendov.B60_63
