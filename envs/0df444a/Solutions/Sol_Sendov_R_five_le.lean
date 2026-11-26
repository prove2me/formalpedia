-- Prove2me | solution 1 for Sendov.R_five_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:15:25.628639+00:00
-- url     : https://prove2.me/submissions/4937aa63-9792-400f-93df-82559d943c4d

import Definitions.Def_Sendov_FiniteRange_Moments
import Definitions.Def_Sendov_FiniteRange_OddBound
import Definitions.Def_Sendov_FiniteRange_Degree5
import Theorems.Thm_Sendov_M_five
import Theorems.Thm_Sendov_integral_five
import Theorems.Thm_Sendov_R_le_of_integral_le


set_option autoImplicit false
open Sendov
open MeasureTheory
variable {α : ℝ}
namespace Sendov
theorem _root_.solution (hα : 0 ≤ α) (hfeas : c 5 α ^ 2 ≤ A 5 α) :
    R 5 α ≤ 1 / 6 + 1 / (4 * (3 + α)) + 1 / 8 + 1 / (16 * (3 + α))
      + 60 * A 5 α ^ 2 / (4 * (3 + α))
        * (3 / 2 * (1 / 4 - 2 * c 5 α / 5 + A 5 α / 6) + 1 / 24) := by
  have h := R_le_of_integral_le (n := 5) (by norm_num) hα (integral_five hfeas)
  rw [M_five] at h
  push_cast at h
  exact h.trans (le_of_eq (by ring))
end Sendov
