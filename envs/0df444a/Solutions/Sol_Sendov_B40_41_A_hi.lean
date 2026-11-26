-- Prove2me | solution 1 for Sendov.B40_41.A_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:35:52.614972+00:00
-- url     : https://prove2.me/submissions/58479dac-ac39-486f-aabc-70d9976c0a4f

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree40_41

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B40_41
namespace Sendov.B40_41
theorem _root_.solution (α : ℝ) : A 41 α = 1 - 2 * α / 40 := by rw [A, M]; push_cast; ring
end Sendov.B40_41
