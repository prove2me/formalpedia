-- Prove2me | solution 1 for Sendov.B38_39.M_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:34:20.447773+00:00
-- url     : https://prove2.me/submissions/0d895b0f-5bb3-47ce-a567-21a18b05190d

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree38_39

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B38_39
namespace Sendov.B38_39
theorem _root_.solution : M 39 = 38 := by norm_num [M]
end Sendov.B38_39
