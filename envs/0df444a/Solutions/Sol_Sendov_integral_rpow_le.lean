-- Prove2me | solution 1 for Sendov.integral_rpow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:02:50.991797+00:00
-- url     : https://prove2.me/submissions/4d343034-7209-4d97-8c24-ba96a36f1671

import Definitions.Def_Sendov_Common_Rpow
import Definitions.Def_Sendov_FiniteRange_OddBound
import Theorems.Thm_Sendov_rpow_add_half_le
import Theorems.Thm_Sendov_Q_nonneg
import Theorems.Thm_Sendov_continuous_integrand


set_option autoImplicit false
open Sendov
open MeasureTheory
variable {n : ℕ} {α q w : ℝ}
namespace Sendov
theorem _root_.solution (hfeas : c n α ^ 2 ≤ A n α) (k : ℕ)
    (hk : ((n : ℝ) - 4) / 2 = (k : ℝ) + 1 / 2) (hw : 0 < w) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ (((n : ℝ) - 4) / 2))
      ≤ ∫ t in (0 : ℝ)..1, t ^ 3 * (Q n α t ^ k * (Q n α t / (2 * w) + w / 2)) := by
  have he : (0 : ℝ) ≤ ((n : ℝ) - 4) / 2 := by rw [hk]; positivity
  refine intervalIntegral.integral_mono_on (by norm_num)
    ((continuous_integrand n α he).intervalIntegrable _ _)
    ((by simp only [Q]; fun_prop : Continuous fun t : ℝ =>
      t ^ 3 * (Q n α t ^ k * (Q n α t / (2 * w) + w / 2))).intervalIntegrable _ _) ?_
  intro t ht
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg ht.1 3)
  rw [hk]
  exact rpow_add_half_le (Q_nonneg hfeas t) k hw
end Sendov
