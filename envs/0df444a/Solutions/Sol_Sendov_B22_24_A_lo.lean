-- Prove2me | solution 1 for Sendov.B22_24.A_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:10:57.129048+00:00
-- url     : https://prove2.me/submissions/f2681690-c774-4f92-ada8-7c96607bfdf3

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree22_24

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B22_24
namespace Sendov.B22_24
theorem _root_.solution (α : ℝ) : A 22 α = 1 - 2 * α / 21 := by rw [A, M]; push_cast; ring
end Sendov.B22_24
