-- Prove2me | solution 1 for Sendov.B28_29.A_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:29:32.942837+00:00
-- url     : https://prove2.me/submissions/32276146-2b42-4b49-afa2-a1a480aaabeb

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree28_29

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B28_29
namespace Sendov.B28_29
theorem _root_.solution (α : ℝ) : A 29 α = 1 - 2 * α / 28 := by rw [A, M]; push_cast; ring
end Sendov.B28_29
