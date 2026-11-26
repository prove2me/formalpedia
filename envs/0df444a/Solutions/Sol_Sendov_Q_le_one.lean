-- Prove2me | solution 1 for Sendov.Q_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:57:02.148226+00:00
-- url     : https://prove2.me/submissions/bdc32010-a074-47e3-b24a-4d30b453123d

import Definitions.Def_Sendov_Defs
import Definitions.Def_Sendov_Common_Basic
import Theorems.Thm_Sendov_three_add_pos
import Theorems.Thm_Sendov_Q_one

set_option autoImplicit false
open Sendov
variable {n : ℕ} {α t : ℝ}
namespace Sendov
theorem _root_.solution (hn : 2 ≤ n) (hα : 0 ≤ α) (hc : 0 ≤ c n α)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : Q n α t ≤ 1 := by
  have hB : Q n α 1 ≤ 1 := by
    rw [Q_one hn hα, div_le_one (three_add_pos hα)]
    linarith
  have hAc : A n α - 2 * c n α ≤ 0 := by
    simp only [Q] at hB
    linarith
  have h5 : A n α * t - 2 * c n α ≤ 0 := by
    rcases le_total 0 (A n α) with h | h
    · nlinarith [mul_le_of_le_one_right h ht1]
    · nlinarith [mul_nonneg ht0 (neg_nonneg.2 h)]
  simp only [Q]
  nlinarith [mul_nonneg ht0 (neg_nonneg.2 h5)]
end Sendov
