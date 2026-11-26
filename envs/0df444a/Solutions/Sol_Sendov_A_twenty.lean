-- Prove2me | solution 1 for Sendov.A_twenty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:18:28.290537+00:00
-- url     : https://prove2.me/submissions/beaa551a-38c6-4599-bb2a-ad24573e803f

import Definitions.Def_Sendov_FiniteRange_Reduce
import Definitions.Def_Sendov_FiniteRange_Degree20

set_option autoImplicit false
set_option maxRecDepth 8000
open Sendov
open MeasureTheory
variable {α : ℝ}
namespace Sendov
theorem _root_.solution (α : ℝ) : A 20 α = 1 - 2 * α / 19 := by
  rw [A, M]
  push_cast
  ring
end Sendov
