-- Prove2me | solution 1 for Sendov.B6_6.A_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:19:25.985658+00:00
-- url     : https://prove2.me/submissions/590b7c03-741e-4e79-a5ac-da5daa4af56b

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree6_6

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B6_6
namespace Sendov.B6_6
theorem _root_.solution (α : ℝ) : A 6 α = 1 - 2 * α / 5 := by rw [A, M]; push_cast; ring
end Sendov.B6_6
