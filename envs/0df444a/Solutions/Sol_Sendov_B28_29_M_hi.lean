-- Prove2me | solution 1 for Sendov.B28_29.M_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:29:21.625942+00:00
-- url     : https://prove2.me/submissions/1cddc6a4-711a-4a18-b409-901d2cc3bd13

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree28_29

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B28_29
namespace Sendov.B28_29
theorem _root_.solution : M 29 = 28 := by norm_num [M]
end Sendov.B28_29
