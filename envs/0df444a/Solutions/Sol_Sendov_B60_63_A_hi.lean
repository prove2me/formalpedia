-- Prove2me | solution 1 for Sendov.B60_63.A_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:46:59.068609+00:00
-- url     : https://prove2.me/submissions/675461fa-a165-4ad7-8bfd-6e412e27fc9a

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree60_63

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B60_63
namespace Sendov.B60_63
theorem _root_.solution (α : ℝ) : A 63 α = 1 - 2 * α / 62 := by rw [A, M]; push_cast; ring
end Sendov.B60_63
