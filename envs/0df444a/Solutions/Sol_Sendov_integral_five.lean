-- Prove2me | solution 1 for Sendov.integral_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:12:36.186181+00:00
-- url     : https://prove2.me/submissions/05bbde21-ada4-4ff9-befe-609f818b9824

import Definitions.Def_Sendov_FiniteRange_Moments
import Definitions.Def_Sendov_FiniteRange_OddBound
import Definitions.Def_Sendov_FiniteRange_Degree5
import Theorems.Thm_Sendov_integral_poly7
import Theorems.Thm_Sendov_integral_rpow_le


set_option autoImplicit false
open Sendov
open MeasureTheory
variable {α : ℝ}
namespace Sendov
theorem _root_.solution (hfeas : c 5 α ^ 2 ≤ A 5 α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 5 α t ^ ((((5 : ℕ) : ℝ) - 4) / 2))
      ≤ 3 / 2 * (1 / 4 - 2 * c 5 α / 5 + A 5 α / 6) + 1 / 24 := by
  have hk : ((((5 : ℕ) : ℝ) - 4) / 2) = ((0 : ℕ) : ℝ) + 1 / 2 := by norm_num
  refine (integral_rpow_le hfeas 0 hk (by norm_num : (0:ℝ) < 1/3)).trans (le_of_eq ?_)
  have hfun : (fun t : ℝ =>
      t ^ 3 * (Q 5 α t ^ 0 * (Q 5 α t / (2 * (1/3)) + (1/3) / 2)))
      = fun t : ℝ => (3 / 2 * 1 + 1 / 6) * t ^ 3 + (3 / 2 * (-2 * c 5 α)) * t ^ 4
          + (3 / 2 * A 5 α) * t ^ 5 + 0 * t ^ 6 + 0 * t ^ 7 := by
    funext t
    simp only [Q]
    ring
  rw [hfun, integral_poly7]
  ring
end Sendov
