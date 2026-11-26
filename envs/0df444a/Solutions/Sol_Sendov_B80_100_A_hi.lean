-- Prove2me | solution 1 for Sendov.B80_100.A_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:00:47.134328+00:00
-- url     : https://prove2.me/submissions/88ef0aa9-390c-473f-b796-53e807dcfb64

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree80_100

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B80_100
namespace Sendov.B80_100
theorem _root_.solution (α : ℝ) : A 100 α = 1 - 2 * α / 99 := by rw [A, M]; push_cast; ring
end Sendov.B80_100
