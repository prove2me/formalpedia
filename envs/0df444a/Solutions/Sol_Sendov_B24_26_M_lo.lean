-- Prove2me | solution 1 for Sendov.B24_26.M_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:27:50.766659+00:00
-- url     : https://prove2.me/submissions/59ed97ed-f9a4-4566-8fd9-93fed0cf5563

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree24_26

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B24_26
namespace Sendov.B24_26
theorem _root_.solution : M 24 = 23 := by norm_num [M]
end Sendov.B24_26
