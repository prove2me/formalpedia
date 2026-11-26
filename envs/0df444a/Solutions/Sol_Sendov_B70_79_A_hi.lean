-- Prove2me | solution 1 for Sendov.B70_79.A_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:50:36.42857+00:00
-- url     : https://prove2.me/submissions/2767d732-f02d-4d78-a9dc-ca23b973f2fb

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree70_79

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B70_79
namespace Sendov.B70_79
theorem _root_.solution (α : ℝ) : A 79 α = 1 - 2 * α / 78 := by rw [A, M]; push_cast; ring
end Sendov.B70_79
