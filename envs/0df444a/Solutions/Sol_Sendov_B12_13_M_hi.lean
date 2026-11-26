-- Prove2me | solution 1 for Sendov.B12_13.M_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:22:14.003466+00:00
-- url     : https://prove2.me/submissions/5e36727b-543e-4eb1-866f-06f71b321b48

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree12_13

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B12_13
namespace Sendov.B12_13
theorem _root_.solution : M 13 = 12 := by norm_num [M]
end Sendov.B12_13
