-- Prove2me | solution 1 for Sendov.B30_31.A_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:11:36.685853+00:00
-- url     : https://prove2.me/submissions/ed649611-efd8-4bc9-8033-9b5b197f8b10

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree30_31

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B30_31
namespace Sendov.B30_31
theorem _root_.solution (α : ℝ) : A 30 α = 1 - 2 * α / 29 := by rw [A, M]; push_cast; ring
end Sendov.B30_31
