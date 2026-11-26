-- Prove2me | solution 1 for Sendov.B36_37.A_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:12:19.098341+00:00
-- url     : https://prove2.me/submissions/283677b6-1879-40bd-ab4b-05bfee49114c

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree36_37

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B36_37
namespace Sendov.B36_37
theorem _root_.solution (α : ℝ) : A 36 α = 1 - 2 * α / 35 := by rw [A, M]; push_cast; ring
end Sendov.B36_37
