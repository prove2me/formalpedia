-- Prove2me | solution 1 for Sendov.B16_18.A_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:24:30.087339+00:00
-- url     : https://prove2.me/submissions/dfa17a99-ce6e-4ae5-a9f7-e35e7abb51e2

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree16_18

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B16_18
namespace Sendov.B16_18
theorem _root_.solution (α : ℝ) : A 18 α = 1 - 2 * α / 17 := by rw [A, M]; push_cast; ring
end Sendov.B16_18
