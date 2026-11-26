-- Prove2me | solution 1 for Sendov.B48_49.A_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:39:22.051824+00:00
-- url     : https://prove2.me/submissions/bcc976f0-91e5-40bd-bffe-35ea9379d0d6

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree48_49

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B48_49
namespace Sendov.B48_49
theorem _root_.solution (α : ℝ) : A 49 α = 1 - 2 * α / 48 := by rw [A, M]; push_cast; ring
end Sendov.B48_49
