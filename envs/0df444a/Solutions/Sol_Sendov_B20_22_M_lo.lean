-- Prove2me | solution 1 for Sendov.B20_22.M_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:26:04.233176+00:00
-- url     : https://prove2.me/submissions/2924472d-d9e8-4afe-a2e2-ee77d4a171db

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree20_22

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B20_22
namespace Sendov.B20_22
theorem _root_.solution : M 20 = 19 := by norm_num [M]
end Sendov.B20_22
