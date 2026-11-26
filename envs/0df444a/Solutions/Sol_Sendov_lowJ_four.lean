-- Prove2me | solution 1 for Sendov.lowJ_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:05:36.45785+00:00
-- url     : https://prove2.me/submissions/6d56bf64-07ce-46b1-8c5a-4437015a54e6

import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_LowDegree
import Theorems.Thm_Sendov_continuous_lowX_pow
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero



set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (a : ℝ) :
    lowJ 4 a = a ^ 4 + 2 * a ^ 3 * (1 - a ^ 2) + 2 * a ^ 2 * (1 - a ^ 2) ^ 2
      + a * (1 - a ^ 2) ^ 3 + (1 - a ^ 2) ^ 4 / 5 := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ =>
      a ^ 4 * s + 2 * a ^ 3 * (1 - a ^ 2) * s ^ 2 + 2 * a ^ 2 * (1 - a ^ 2) ^ 2 * s ^ 3
        + a * (1 - a ^ 2) ^ 3 * s ^ 4 + (1 - a ^ 2) ^ 4 / 5 * s ^ 5) (lowX a t ^ 4) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => a ^ 4 * s) (a ^ 4 * 1) t :=
      (hasDerivAt_id' (x := t)).const_mul _
    have h2 : HasDerivAt (fun s : ℝ => 2 * a ^ 3 * (1 - a ^ 2) * s ^ 2)
        (2 * a ^ 3 * (1 - a ^ 2) * (2 * t)) t := by
      simpa using (hasDerivAt_pow 2 t).const_mul (2 * a ^ 3 * (1 - a ^ 2))
    have h3 : HasDerivAt (fun s : ℝ => 2 * a ^ 2 * (1 - a ^ 2) ^ 2 * s ^ 3)
        (2 * a ^ 2 * (1 - a ^ 2) ^ 2 * (3 * t ^ 2)) t := by
      simpa using (hasDerivAt_pow 3 t).const_mul (2 * a ^ 2 * (1 - a ^ 2) ^ 2)
    have h4 : HasDerivAt (fun s : ℝ => a * (1 - a ^ 2) ^ 3 * s ^ 4)
        (a * (1 - a ^ 2) ^ 3 * (4 * t ^ 3)) t := by
      simpa using (hasDerivAt_pow 4 t).const_mul (a * (1 - a ^ 2) ^ 3)
    have h5 : HasDerivAt (fun s : ℝ => (1 - a ^ 2) ^ 4 / 5 * s ^ 5)
        ((1 - a ^ 2) ^ 4 / 5 * (5 * t ^ 4)) t := by
      simpa using (hasDerivAt_pow 5 t).const_mul ((1 - a ^ 2) ^ 4 / 5)
    have hval : lowX a t ^ 4 = a ^ 4 * 1 + 2 * a ^ 3 * (1 - a ^ 2) * (2 * t)
        + 2 * a ^ 2 * (1 - a ^ 2) ^ 2 * (3 * t ^ 2) + a * (1 - a ^ 2) ^ 3 * (4 * t ^ 3)
        + (1 - a ^ 2) ^ 4 / 5 * (5 * t ^ 4) := by
      simp only [lowX]
      ring
    rw [hval]
    exact ((((h1.add h2).add h3).add h4).add h5)
  rw [lowJ, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    ((continuous_lowX_pow a 4).intervalIntegrable _ _)]
  norm_num
end Sendov
