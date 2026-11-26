-- Prove2me | solution 1 for Sendov.B8_9.A_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:21:14.133798+00:00
-- url     : https://prove2.me/submissions/4756c05c-86df-407e-bbaf-32cf4b0fa17f

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree8_9

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B8_9
namespace Sendov.B8_9
theorem _root_.solution (α : ℝ) : A 9 α = 1 - 2 * α / 8 := by rw [A, M]; push_cast; ring
end Sendov.B8_9
