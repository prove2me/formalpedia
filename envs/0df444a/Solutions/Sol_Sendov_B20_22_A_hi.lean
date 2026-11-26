-- Prove2me | solution 1 for Sendov.B20_22.A_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:26:12.535827+00:00
-- url     : https://prove2.me/submissions/77b93ff0-548a-485f-8185-daa08ee66e45

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree20_22

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B20_22
namespace Sendov.B20_22
theorem _root_.solution (α : ℝ) : A 22 α = 1 - 2 * α / 21 := by rw [A, M]; push_cast; ring
end Sendov.B20_22
