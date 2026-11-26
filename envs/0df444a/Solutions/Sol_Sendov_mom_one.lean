-- Prove2me | solution 1 for Sendov.mom_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:08:24.622893+00:00
-- url     : https://prove2.me/submissions/bcbe8180-e213-4e86-a442-7917785972c1

import Definitions.Def_Sendov_FiniteRange_Moments
import Definitions.Def_Sendov_FiniteRange_OddBound
import Definitions.Def_Sendov_FiniteRange_Reduce

set_option autoImplicit false
open Sendov
open MeasureTheory Finset
variable {n : ℕ} {α w : ℝ}
namespace Sendov
theorem _root_.solution (n : ℕ) (α : ℝ) : mom n α 1 = 1 / 4 - 2 * c n α / 5 + A n α / 6 := by
  simp [mom, Finset.sum_range_succ]
  ring
end Sendov
