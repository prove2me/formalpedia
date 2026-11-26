-- Prove2me | solution 1 for Sendov.B80_100.M_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:00:44.747484+00:00
-- url     : https://prove2.me/submissions/af4263c4-4e03-45e2-b952-a62dfcbf4e50

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree80_100

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B80_100
namespace Sendov.B80_100
theorem _root_.solution : M 100 = 99 := by norm_num [M]
end Sendov.B80_100
