-- Prove2me | solution 1 for Sendov.c_twenty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:18:29.631868+00:00
-- url     : https://prove2.me/submissions/293056d0-513e-435d-888d-efde88524a79

import Definitions.Def_Sendov_FiniteRange_Reduce
import Definitions.Def_Sendov_FiniteRange_Degree20

set_option autoImplicit false
set_option maxRecDepth 8000
open Sendov
open MeasureTheory
variable {α : ℝ}
namespace Sendov
theorem _root_.solution (α : ℝ) : c 20 α = 1 - α / 19 - α / (2 * (3 + α)) := by
  rw [c, M]
  push_cast
  ring
end Sendov
