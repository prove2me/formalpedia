-- Prove2me | solution 1 for Sendov.B26_27.M_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:28:29.223979+00:00
-- url     : https://prove2.me/submissions/aa0a5b8d-35af-4f31-8812-291d7683ea78

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree26_27

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B26_27
namespace Sendov.B26_27
theorem _root_.solution : M 26 = 25 := by norm_num [M]
end Sendov.B26_27
