-- Prove2me | solution 1 for Sendov.integral_le_mom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:08:18.558319+00:00
-- url     : https://prove2.me/submissions/b29f9731-6787-41a6-8cda-03d949503473

import Definitions.Def_Sendov_FiniteRange_Moments
import Definitions.Def_Sendov_FiniteRange_OddBound
import Definitions.Def_Sendov_FiniteRange_Reduce
import Theorems.Thm_Sendov_integral_moment
import Theorems.Thm_Sendov_integral_rpow_le


set_option autoImplicit false
open Sendov
open MeasureTheory Finset
variable {n : ℕ} {α w : ℝ}
namespace Sendov
theorem _root_.solution (hfeas : c n α ^ 2 ≤ A n α) (k : ℕ)
    (hk : ((n : ℝ) - 4) / 2 = (k : ℝ) + 1 / 2) (hw : 0 < w) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ (((n : ℝ) - 4) / 2))
      ≤ mom n α (k + 1) / (2 * w) + w / 2 * mom n α k := by
  refine (integral_rpow_le hfeas k hk hw).trans (le_of_eq ?_)
  have hfun : (fun t : ℝ => t ^ 3 * (Q n α t ^ k * (Q n α t / (2 * w) + w / 2)))
      = fun t : ℝ => 1 / (2 * w) * (t ^ 3 * Q n α t ^ (k + 1))
          + w / 2 * (t ^ 3 * Q n α t ^ k) := by
    funext t
    rw [pow_succ]
    ring
  have hi : ∀ j : ℕ, ∀ a : ℝ,
      IntervalIntegrable (fun t : ℝ => a * (t ^ 3 * Q n α t ^ j)) volume 0 1 := by
    intro j a
    exact (by simp only [Q]; fun_prop :
      Continuous fun t : ℝ => a * (t ^ 3 * Q n α t ^ j)).intervalIntegrable _ _
  rw [hfun, intervalIntegral.integral_add (hi (k + 1) _) (hi k _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_moment, integral_moment]
  ring
end Sendov
