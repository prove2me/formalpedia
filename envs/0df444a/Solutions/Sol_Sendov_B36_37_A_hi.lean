-- Prove2me | solution 1 for Sendov.B36_37.A_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:33:54.282808+00:00
-- url     : https://prove2.me/submissions/bca07826-df90-418b-96a2-5545241e1332

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree36_37

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B36_37
namespace Sendov.B36_37
theorem _root_.solution (α : ℝ) : A 37 α = 1 - 2 * α / 36 := by rw [A, M]; push_cast; ring
end Sendov.B36_37
