-- Prove2me | solution 1 for Sendov.B42_43.A_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:36:31.978798+00:00
-- url     : https://prove2.me/submissions/45fe0364-4d0e-4c6c-a43e-71603a83145d

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree42_43

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B42_43
namespace Sendov.B42_43
theorem _root_.solution (α : ℝ) : A 43 α = 1 - 2 * α / 42 := by rw [A, M]; push_cast; ring
end Sendov.B42_43
