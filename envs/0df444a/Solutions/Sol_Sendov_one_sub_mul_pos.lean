-- Prove2me | solution 1 for Sendov.one_sub_mul_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:00:43.455068+00:00
-- url     : https://prove2.me/submissions/8cad870d-0027-4da1-9809-eb520b27e2eb

import Definitions.Def_Sendov_Reduction_Stat
import Definitions.Def_Sendov_Reduction_Simplified

set_option autoImplicit false
open Sendov
open MeasureTheory
variable {n : ℕ} {a x t α : ℝ}
namespace Sendov
theorem _root_.solution (ha : 0 < a) (ha1 : a < 1) (hx : x ^ 2 ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 < 1 - a * x * t := by
  rcases le_or_gt x 0 with h | h
  · nlinarith [mul_nonneg ht0 (mul_nonneg ha.le (neg_nonneg.2 h))]
  · have hx1 : x ≤ 1 := by nlinarith
    have h1 : a * x * t ≤ a * x * 1 :=
      mul_le_mul_of_nonneg_left ht1 (mul_pos ha h).le
    nlinarith [h1]
end Sendov
