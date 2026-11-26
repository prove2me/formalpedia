-- Prove2me | solution 1 for Sendov.B24_26.M_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:27:54.061531+00:00
-- url     : https://prove2.me/submissions/ce81e91d-3728-4261-a265-02136bec8195

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree24_26

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B24_26
namespace Sendov.B24_26
theorem _root_.solution : M 26 = 25 := by norm_num [M]
end Sendov.B24_26
