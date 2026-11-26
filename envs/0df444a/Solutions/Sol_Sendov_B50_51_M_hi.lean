-- Prove2me | solution 1 for Sendov.B50_51.M_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:39:59.381804+00:00
-- url     : https://prove2.me/submissions/308ba309-e74c-4a3a-815a-c9586a5e83d9

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree50_51

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B50_51
namespace Sendov.B50_51
theorem _root_.solution : M 51 = 50 := by norm_num [M]
end Sendov.B50_51
