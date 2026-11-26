-- Prove2me | solution 1 for Sendov.A_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:12:31.05959+00:00
-- url     : https://prove2.me/submissions/14d9f1a9-7617-4683-9c20-603f49add9d9

import Definitions.Def_Sendov_FiniteRange_Moments
import Definitions.Def_Sendov_FiniteRange_OddBound
import Definitions.Def_Sendov_FiniteRange_Degree5

set_option autoImplicit false
open Sendov
open MeasureTheory
variable {α : ℝ}
namespace Sendov
theorem _root_.solution (α : ℝ) : A 5 α = 1 - α / 2 := by
  rw [A, M]
  push_cast
  ring
end Sendov
