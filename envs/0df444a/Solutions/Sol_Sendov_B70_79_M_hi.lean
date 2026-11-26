-- Prove2me | solution 1 for Sendov.B70_79.M_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:50:28.178251+00:00
-- url     : https://prove2.me/submissions/7952ef2c-3613-4b05-93d0-a1aecb879977

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree70_79

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B70_79
namespace Sendov.B70_79
theorem _root_.solution : M 79 = 78 := by norm_num [M]
end Sendov.B70_79
