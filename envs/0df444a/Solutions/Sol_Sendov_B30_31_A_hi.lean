-- Prove2me | solution 1 for Sendov.B30_31.A_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:30:40.054418+00:00
-- url     : https://prove2.me/submissions/e0271cd7-9c37-45fb-a4cb-215f64afd310

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree30_31

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B30_31
namespace Sendov.B30_31
theorem _root_.solution (α : ℝ) : A 31 α = 1 - 2 * α / 30 := by rw [A, M]; push_cast; ring
end Sendov.B30_31
