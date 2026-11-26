-- Prove2me | solution 1 for Sendov.B64_69.M_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:47:28.236838+00:00
-- url     : https://prove2.me/submissions/fd154c76-e3ea-487c-8636-87e2eec9583e

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree64_69

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B64_69
namespace Sendov.B64_69
theorem _root_.solution : M 64 = 63 := by norm_num [M]
end Sendov.B64_69
