-- Prove2me | solution 1 for Sendov.B50_51.A_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:40:19.827972+00:00
-- url     : https://prove2.me/submissions/da4a6ea9-572c-422c-b0da-17a5d89d2d14

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree50_51

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B50_51
namespace Sendov.B50_51
theorem _root_.solution (α : ℝ) : A 51 α = 1 - 2 * α / 50 := by rw [A, M]; push_cast; ring
end Sendov.B50_51
