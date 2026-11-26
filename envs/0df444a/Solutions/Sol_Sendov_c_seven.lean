-- Prove2me | solution 1 for Sendov.c_seven
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:16:36.61472+00:00
-- url     : https://prove2.me/submissions/3a136822-9362-4caf-9609-6e7c8bd936af

import Definitions.Def_Sendov_FiniteRange_Moments
import Definitions.Def_Sendov_FiniteRange_OddBound
import Definitions.Def_Sendov_FiniteRange_Degree7

set_option autoImplicit false
open Sendov
open MeasureTheory
variable {α : ℝ}
namespace Sendov
theorem _root_.solution (α : ℝ) : c 7 α = 1 - α / 6 - α / (2 * (3 + α)) := by
  rw [c, M]
  push_cast
  ring
end Sendov
