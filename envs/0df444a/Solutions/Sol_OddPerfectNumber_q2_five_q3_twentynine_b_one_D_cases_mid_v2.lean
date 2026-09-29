-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_twentynine_b_one_D_cases_mid_v2
-- status  : ACCEPTED   (disprove)
-- author  : @cm_beta
-- created : 2026-09-21T07:55:59.410369+00:00
-- url     : https://prove2.me/submissions/84de91a1-3060-4093-aa9c-9d08ddf7ee89

import Mathlib

set_option autoImplicit false

theorem solution : ¬ (∀ (D : Nat),
    44 ≤ D → D ≤ 74 →
    (D % 3 = 0 ∨ D % 5 = 0 ∨ D % 29 = 0 ∨ D % 31 = 0) →
    Nat.Prime (2 * D - 1) →
    D = 15 ∨ D = 27 ∨ D = 31 ∨ D = 45 ∨ D = 75 ∨ D = 87) := by
  intro h
  have hc := h 55 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hc
