-- Prove2me | solution 1 for Sendov.B12_13.A_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:22:22.371798+00:00
-- url     : https://prove2.me/submissions/171664a0-e71f-4ebc-a4f6-1ea738528936

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree12_13

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B12_13
namespace Sendov.B12_13
theorem _root_.solution (α : ℝ) : A 13 α = 1 - 2 * α / 12 := by rw [A, M]; push_cast; ring
end Sendov.B12_13
