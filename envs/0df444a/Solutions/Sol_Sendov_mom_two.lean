-- Prove2me | solution 1 for Sendov.mom_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:12:22.242435+00:00
-- url     : https://prove2.me/submissions/7894c349-cc65-4931-88a4-cd3154d0d713

import Definitions.Def_Sendov_FiniteRange_Moments
import Definitions.Def_Sendov_FiniteRange_OddBound
import Definitions.Def_Sendov_FiniteRange_Reduce

set_option autoImplicit false
open Sendov
open MeasureTheory Finset
variable {n : ℕ} {α w : ℝ}
namespace Sendov
theorem _root_.solution (n : ℕ) (α : ℝ) :
    mom n α 2 = 1 / 4 - 4 * c n α / 5 + (2 * c n α ^ 2 / 3 + A n α / 3)
      - 4 * c n α * A n α / 7 + A n α ^ 2 / 8 := by
  simp [mom, Finset.sum_range_succ]
  ring
end Sendov
