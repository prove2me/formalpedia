-- Prove2me | solution 1 for Sendov.B50_51.M_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:39:57.595395+00:00
-- url     : https://prove2.me/submissions/64e85656-fe67-4253-823b-150fcf3658c1

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree50_51

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B50_51
namespace Sendov.B50_51
theorem _root_.solution : M 50 = 49 := by norm_num [M]
end Sendov.B50_51
