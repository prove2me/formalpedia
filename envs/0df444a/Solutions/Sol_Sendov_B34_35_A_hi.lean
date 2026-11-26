-- Prove2me | solution 1 for Sendov.B34_35.A_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:33:07.695795+00:00
-- url     : https://prove2.me/submissions/f1a79cba-6d40-4192-82ed-37be4984be7d

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree34_35

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B34_35
namespace Sendov.B34_35
theorem _root_.solution (α : ℝ) : A 35 α = 1 - 2 * α / 34 := by rw [A, M]; push_cast; ring
end Sendov.B34_35
