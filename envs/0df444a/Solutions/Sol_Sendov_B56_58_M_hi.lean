-- Prove2me | solution 1 for Sendov.B56_58.M_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:43:23.315839+00:00
-- url     : https://prove2.me/submissions/5365d9e2-8c7e-48a0-aceb-342ab485607b

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree56_58

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B56_58
namespace Sendov.B56_58
theorem _root_.solution : M 58 = 57 := by norm_num [M]
end Sendov.B56_58
