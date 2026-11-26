-- Prove2me | solution 1 for Sendov.B30_31.M_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:30:32.828045+00:00
-- url     : https://prove2.me/submissions/209e4611-6088-4b7e-a8e5-5149df099aed

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree30_31

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B30_31
namespace Sendov.B30_31
theorem _root_.solution : M 31 = 30 := by norm_num [M]
end Sendov.B30_31
