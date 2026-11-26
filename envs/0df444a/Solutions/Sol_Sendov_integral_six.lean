-- Prove2me | solution 1 for Sendov.integral_six
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:15:36.085747+00:00
-- url     : https://prove2.me/submissions/1e0fedab-8925-49f6-a95b-63980f60ad35

import Definitions.Def_Sendov_Common_Basic
import Definitions.Def_Sendov_FiniteRange_Moments
import Definitions.Def_Sendov_FiniteRange_Degree6
import Theorems.Thm_Sendov_integral_poly7


set_option autoImplicit false
open Sendov
open MeasureTheory
variable {α : ℝ}
namespace Sendov
theorem _root_.solution (α : ℝ) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 6 α t ^ ((((6 : ℕ) : ℝ) - 4) / 2))
      = 1 / 4 - 2 * c 6 α / 5 + A 6 α / 6 := by
  have hfun : (fun t : ℝ => t ^ 3 * Q 6 α t ^ ((((6 : ℕ) : ℝ) - 4) / 2))
      = fun t : ℝ => 1 * t ^ 3 + (-2 * c 6 α) * t ^ 4 + A 6 α * t ^ 5 + 0 * t ^ 6
          + 0 * t ^ 7 := by
    funext t
    rw [show ((((6 : ℕ) : ℝ) - 4) / 2) = 1 by norm_num, Real.rpow_one, Q]
    ring
  rw [hfun, integral_poly7]
  ring
end Sendov
