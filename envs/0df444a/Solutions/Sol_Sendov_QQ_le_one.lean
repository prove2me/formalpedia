-- Prove2me | solution 1 for Sendov.QQ_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:07:43.041853+00:00
-- url     : https://prove2.me/submissions/f72714bb-8414-47a2-9c3a-77fc46cf2ad4

import Definitions.Def_Sendov_Common_Rpow
import Definitions.Def_Sendov_Common_Quadratic
import Theorems.Thm_Sendov_QQ_one

set_option autoImplicit false
open Sendov
variable {c A t : ℝ}
namespace Sendov
theorem _root_.solution (hc : 0 ≤ c) (hB : QQ c A 1 ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    QQ c A t ≤ 1 := by
  have hAc : A - 2 * c ≤ 0 := by rw [QQ_one] at hB; linarith
  have h5 : A * t - 2 * c ≤ 0 := by
    rcases le_total 0 A with h | h
    · nlinarith [mul_le_of_le_one_right h ht1]
    · nlinarith [mul_nonneg ht0 (neg_nonneg.2 h)]
  simp only [QQ]
  nlinarith [mul_nonneg ht0 (neg_nonneg.2 h5)]
end Sendov
