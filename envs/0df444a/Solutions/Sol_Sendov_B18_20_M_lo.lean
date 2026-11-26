-- Prove2me | solution 1 for Sendov.B18_20.M_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:25:04.267703+00:00
-- url     : https://prove2.me/submissions/58724f82-fff4-4122-a05d-a0e6ff08f59a

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree18_20

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B18_20
namespace Sendov.B18_20
theorem _root_.solution : M 18 = 17 := by norm_num [M]
end Sendov.B18_20
