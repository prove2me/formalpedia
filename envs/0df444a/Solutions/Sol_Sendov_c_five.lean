-- Prove2me | solution 1 for Sendov.c_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:12:34.837235+00:00
-- url     : https://prove2.me/submissions/ebc305c0-7f38-4350-a89f-cc916457201e

import Definitions.Def_Sendov_FiniteRange_Moments
import Definitions.Def_Sendov_FiniteRange_OddBound
import Definitions.Def_Sendov_FiniteRange_Degree5

set_option autoImplicit false
open Sendov
open MeasureTheory
variable {α : ℝ}
namespace Sendov
theorem _root_.solution (α : ℝ) : c 5 α = 1 - α / 4 - α / (2 * (3 + α)) := by
  rw [c, M]
  push_cast
  ring
end Sendov
