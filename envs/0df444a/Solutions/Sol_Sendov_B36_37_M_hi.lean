-- Prove2me | solution 1 for Sendov.B36_37.M_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:33:36.320729+00:00
-- url     : https://prove2.me/submissions/b06b1dfc-04ca-4d00-8e7a-a172a87c9842

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree36_37

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B36_37
namespace Sendov.B36_37
theorem _root_.solution : M 37 = 36 := by norm_num [M]
end Sendov.B36_37
