-- Prove2me | solution 1 for Sendov.B60_63.A_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:14:23.5508+00:00
-- url     : https://prove2.me/submissions/ce4c9426-cb2a-475d-a65d-acba4d8dd040

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree60_63

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B60_63
namespace Sendov.B60_63
theorem _root_.solution (α : ℝ) : A 60 α = 1 - 2 * α / 59 := by rw [A, M]; push_cast; ring
end Sendov.B60_63
