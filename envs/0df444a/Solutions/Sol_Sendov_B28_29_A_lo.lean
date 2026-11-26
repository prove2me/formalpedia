-- Prove2me | solution 1 for Sendov.B28_29.A_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:11:30.440476+00:00
-- url     : https://prove2.me/submissions/363c4201-5678-4581-bf01-0bf3b2854bc9

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree28_29

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B28_29
namespace Sendov.B28_29
theorem _root_.solution (α : ℝ) : A 28 α = 1 - 2 * α / 27 := by rw [A, M]; push_cast; ring
end Sendov.B28_29
