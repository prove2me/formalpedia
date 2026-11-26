-- Prove2me | solution 1 for Sendov.B64_69.A_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:14:31.848991+00:00
-- url     : https://prove2.me/submissions/b17992e4-abc7-4723-b91a-9ce5428a6485

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree64_69

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B64_69
namespace Sendov.B64_69
theorem _root_.solution (α : ℝ) : A 64 α = 1 - 2 * α / 63 := by rw [A, M]; push_cast; ring
end Sendov.B64_69
