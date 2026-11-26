-- Prove2me | solution 1 for Sendov.B26_27.A_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:28:54.58683+00:00
-- url     : https://prove2.me/submissions/8a2bfa2d-595f-476c-90c4-17d3a1545e0d

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree26_27

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B26_27
namespace Sendov.B26_27
theorem _root_.solution (α : ℝ) : A 27 α = 1 - 2 * α / 26 := by rw [A, M]; push_cast; ring
end Sendov.B26_27
