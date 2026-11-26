-- Prove2me | solution 1 for Sendov.B18_20.A_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:25:09.636372+00:00
-- url     : https://prove2.me/submissions/cb67cdfd-2845-441e-8700-3e477449fc7f

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree18_20

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B18_20
namespace Sendov.B18_20
theorem _root_.solution (α : ℝ) : A 20 α = 1 - 2 * α / 19 := by rw [A, M]; push_cast; ring
end Sendov.B18_20
