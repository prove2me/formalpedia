-- Prove2me | solution 1 for Sendov.B22_24.A_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:27:42.944391+00:00
-- url     : https://prove2.me/submissions/7ce710d1-296e-4baa-a7bc-605a23df37d3

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree22_24

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B22_24
namespace Sendov.B22_24
theorem _root_.solution (α : ℝ) : A 24 α = 1 - 2 * α / 23 := by rw [A, M]; push_cast; ring
end Sendov.B22_24
