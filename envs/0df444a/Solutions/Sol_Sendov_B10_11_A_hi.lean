-- Prove2me | solution 1 for Sendov.B10_11.A_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:21:44.149802+00:00
-- url     : https://prove2.me/submissions/f2ca1e4f-4c27-4961-a3bb-b135f3122921

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree10_11

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B10_11
namespace Sendov.B10_11
theorem _root_.solution (α : ℝ) : A 11 α = 1 - 2 * α / 10 := by rw [A, M]; push_cast; ring
end Sendov.B10_11
