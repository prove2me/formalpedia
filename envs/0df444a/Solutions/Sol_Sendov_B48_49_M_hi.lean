-- Prove2me | solution 1 for Sendov.B48_49.M_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:39:12.574718+00:00
-- url     : https://prove2.me/submissions/a176b9a3-453d-4e1f-a54c-6df32e7e8e73

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree48_49

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B48_49
namespace Sendov.B48_49
theorem _root_.solution : M 49 = 48 := by norm_num [M]
end Sendov.B48_49
