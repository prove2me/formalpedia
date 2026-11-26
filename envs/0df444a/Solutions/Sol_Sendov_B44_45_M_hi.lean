-- Prove2me | solution 1 for Sendov.B44_45.M_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:37:48.826665+00:00
-- url     : https://prove2.me/submissions/5493ede6-dbc3-481d-94b0-e5881584a939

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree44_45

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B44_45
namespace Sendov.B44_45
theorem _root_.solution : M 45 = 44 := by norm_num [M]
end Sendov.B44_45
