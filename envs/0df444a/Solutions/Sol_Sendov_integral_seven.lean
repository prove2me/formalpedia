-- Prove2me | solution 1 for Sendov.integral_seven
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:16:43.643799+00:00
-- url     : https://prove2.me/submissions/db205094-e8e9-43f7-8507-788b531f9a74

import Definitions.Def_Sendov_FiniteRange_Moments
import Definitions.Def_Sendov_FiniteRange_OddBound
import Definitions.Def_Sendov_FiniteRange_Degree7
import Theorems.Thm_Sendov_integral_poly7
import Theorems.Thm_Sendov_integral_rpow_le


set_option autoImplicit false
open Sendov
open MeasureTheory
variable {α : ℝ}
namespace Sendov
theorem _root_.solution (hfeas : c 7 α ^ 2 ≤ A 7 α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 7 α t ^ ((((7 : ℕ) : ℝ) - 4) / 2))
      ≤ 1 / 4 - 3 * c 7 α / 5 + (4 * c 7 α ^ 2 + 3 * A 7 α) / 12
        - 2 * c 7 α * A 7 α / 7 + A 7 α ^ 2 / 16 := by
  have hk : ((((7 : ℕ) : ℝ) - 4) / 2) = ((1 : ℕ) : ℝ) + 1 / 2 := by norm_num
  refine (integral_rpow_le hfeas 1 hk one_pos).trans (le_of_eq ?_)
  have hfun : (fun t : ℝ => t ^ 3 * (Q 7 α t ^ 1 * (Q 7 α t / (2 * 1) + 1 / 2)))
      = fun t : ℝ => 1 * t ^ 3 + (-3 * c 7 α) * t ^ 4
          + ((4 * c 7 α ^ 2 + 3 * A 7 α) / 2) * t ^ 5 + (-2 * c 7 α * A 7 α) * t ^ 6
          + (A 7 α ^ 2 / 2) * t ^ 7 := by
    funext t
    simp only [Q]
    ring
  rw [hfun, integral_poly7]
  ring
end Sendov
