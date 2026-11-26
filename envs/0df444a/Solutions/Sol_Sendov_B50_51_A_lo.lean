-- Prove2me | solution 1 for Sendov.B50_51.A_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:13:22.471555+00:00
-- url     : https://prove2.me/submissions/e852a72e-7d49-4abf-8772-ffac9f07b801

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree50_51

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B50_51
namespace Sendov.B50_51
theorem _root_.solution (α : ℝ) : A 50 α = 1 - 2 * α / 49 := by rw [A, M]; push_cast; ring
end Sendov.B50_51
