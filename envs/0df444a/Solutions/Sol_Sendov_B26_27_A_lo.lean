-- Prove2me | solution 1 for Sendov.B26_27.A_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:11:14.888353+00:00
-- url     : https://prove2.me/submissions/2b25cf74-04eb-4ceb-a1c1-891053f3a4fc

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree26_27

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B26_27
namespace Sendov.B26_27
theorem _root_.solution (α : ℝ) : A 26 α = 1 - 2 * α / 25 := by rw [A, M]; push_cast; ring
end Sendov.B26_27
