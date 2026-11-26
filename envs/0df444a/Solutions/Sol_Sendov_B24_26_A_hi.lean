-- Prove2me | solution 1 for Sendov.B24_26.A_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:28:12.008103+00:00
-- url     : https://prove2.me/submissions/50bedc57-6c72-4571-85a5-8d70ad40ee5f

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree24_26

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B24_26
namespace Sendov.B24_26
theorem _root_.solution (α : ℝ) : A 26 α = 1 - 2 * α / 25 := by rw [A, M]; push_cast; ring
end Sendov.B24_26
