-- Prove2me | solution 1 for Sendov.B18_20.A_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:10:40.994082+00:00
-- url     : https://prove2.me/submissions/e019a681-6f64-4c5a-b7ae-175c8a351b32

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree18_20

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B18_20
namespace Sendov.B18_20
theorem _root_.solution (α : ℝ) : A 18 α = 1 - 2 * α / 17 := by rw [A, M]; push_cast; ring
end Sendov.B18_20
