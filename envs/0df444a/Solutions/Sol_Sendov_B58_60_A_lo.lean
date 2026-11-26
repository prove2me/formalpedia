-- Prove2me | solution 1 for Sendov.B58_60.A_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:14:09.107173+00:00
-- url     : https://prove2.me/submissions/18a35a21-55ec-4fd5-a178-89f6493fc1c6

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree58_60

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B58_60
namespace Sendov.B58_60
theorem _root_.solution (α : ℝ) : A 58 α = 1 - 2 * α / 57 := by rw [A, M]; push_cast; ring
end Sendov.B58_60
