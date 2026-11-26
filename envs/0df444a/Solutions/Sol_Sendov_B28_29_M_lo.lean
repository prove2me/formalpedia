-- Prove2me | solution 1 for Sendov.B28_29.M_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:29:19.771555+00:00
-- url     : https://prove2.me/submissions/bc81f382-8af9-4577-aa2f-9b189b797e7e

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree28_29

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B28_29
namespace Sendov.B28_29
theorem _root_.solution : M 28 = 27 := by norm_num [M]
end Sendov.B28_29
