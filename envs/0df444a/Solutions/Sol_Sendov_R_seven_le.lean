-- Prove2me | solution 1 for Sendov.R_seven_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:17:58.653318+00:00
-- url     : https://prove2.me/submissions/f1c95cbc-ff54-4f23-8025-cd331bd3058e

import Definitions.Def_Sendov_FiniteRange_Moments
import Definitions.Def_Sendov_FiniteRange_OddBound
import Definitions.Def_Sendov_FiniteRange_Degree7
import Theorems.Thm_Sendov_M_seven
import Theorems.Thm_Sendov_integral_seven
import Theorems.Thm_Sendov_R_le_of_integral_le


set_option autoImplicit false
open Sendov
open MeasureTheory
variable {α : ℝ}
namespace Sendov
theorem _root_.solution (hα : 0 ≤ α) (hfeas : c 7 α ^ 2 ≤ A 7 α) :
    R 7 α ≤ 1 / 6 + 1 / (4 * (3 + α)) + 1 / 12 + 1 / (24 * (3 + α))
      + 210 * A 7 α ^ 2 / (4 * (3 + α))
        * (1 / 4 - 3 * c 7 α / 5 + (4 * c 7 α ^ 2 + 3 * A 7 α) / 12
          - 2 * c 7 α * A 7 α / 7 + A 7 α ^ 2 / 16) := by
  have h := R_le_of_integral_le (n := 7) (by norm_num) hα (integral_seven hfeas)
  rw [M_seven] at h
  push_cast at h
  exact h.trans (le_of_eq (by ring))
end Sendov
