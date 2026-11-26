-- Prove2me | solution 1 for Sendov.B40_41.M_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:35:42.145839+00:00
-- url     : https://prove2.me/submissions/c7024660-9857-4934-b653-581fad22a71f

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree40_41

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B40_41
namespace Sendov.B40_41
theorem _root_.solution : M 40 = 39 := by norm_num [M]
end Sendov.B40_41
