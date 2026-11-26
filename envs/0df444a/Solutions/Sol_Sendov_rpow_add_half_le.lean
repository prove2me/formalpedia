-- Prove2me | solution 1 for Sendov.rpow_add_half_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:00:51.610378+00:00
-- url     : https://prove2.me/submissions/b02ba224-8306-4bd6-9827-fc27a255a791

import Definitions.Def_Sendov_Common_Rpow
import Definitions.Def_Sendov_FiniteRange_OddBound
import Theorems.Thm_Sendov_sqrt_le_tangent

set_option autoImplicit false
open Sendov
open MeasureTheory
variable {n : ℕ} {α q w : ℝ}
namespace Sendov
theorem _root_.solution (hq : 0 ≤ q) (k : ℕ) (hw : 0 < w) :
    q ^ ((k : ℝ) + 1 / 2) ≤ q ^ k * (q / (2 * w) + w / 2) := by
  rcases hq.lt_or_eq with h | h
  · have he : q ^ ((k : ℝ) + 1 / 2) = q ^ k * Real.sqrt q := by
      rw [Real.rpow_add h, Real.rpow_natCast, Real.sqrt_eq_rpow]
    rw [he]
    exact mul_le_mul_of_nonneg_left (sqrt_le_tangent hq hw) (pow_nonneg hq k)
  · rw [← h, Real.zero_rpow (by positivity)]
    refine mul_nonneg (pow_nonneg le_rfl k) ?_
    rw [zero_div]
    linarith
end Sendov
