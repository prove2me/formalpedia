-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_twentynine_b_one_D_cases_loa_v2
-- status  : ACCEPTED   (disprove)
-- author  : @cm_beta
-- created : 2026-09-21T07:55:58.392723+00:00
-- url     : https://prove2.me/submissions/36fc86ba-20fc-4226-991b-401b1c0d1087

import Mathlib

set_option autoImplicit false

theorem solution : ¬ (∀ (D : Nat),
    12 ≤ D → D ≤ 27 →
    (D % 3 = 0 ∨ D % 5 = 0 ∨ D % 29 = 0 ∨ D % 31 = 0) →
    Nat.Prime (2 * D - 1) →
    D = 15 ∨ D = 27 ∨ D = 31 ∨ D = 45 ∨ D = 75 ∨ D = 87) := by
  intro h
  have hc := h 21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hc
