-- Prove2me | solution 1 for Sendov.B26_27.M_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:28:37.476774+00:00
-- url     : https://prove2.me/submissions/94a363e1-7b18-47f2-9e71-4b15009d7076

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree26_27

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B26_27
namespace Sendov.B26_27
theorem _root_.solution : M 27 = 26 := by norm_num [M]
end Sendov.B26_27
