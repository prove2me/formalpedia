-- Prove2me | solution 1 for Sendov.B56_58.A_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:44:08.842134+00:00
-- url     : https://prove2.me/submissions/c1bb36fc-927f-4005-ae5f-4edf86b5c3cc

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree56_58

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B56_58
namespace Sendov.B56_58
theorem _root_.solution (α : ℝ) : A 58 α = 1 - 2 * α / 57 := by rw [A, M]; push_cast; ring
end Sendov.B56_58
