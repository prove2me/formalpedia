-- Prove2me | solution 1 for Sendov.B52_53.A_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:13:30.481048+00:00
-- url     : https://prove2.me/submissions/1676d0b6-2fd0-4882-b0ee-78a5375a7746

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree52_53

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B52_53
namespace Sendov.B52_53
theorem _root_.solution (α : ℝ) : A 52 α = 1 - 2 * α / 51 := by rw [A, M]; push_cast; ring
end Sendov.B52_53
