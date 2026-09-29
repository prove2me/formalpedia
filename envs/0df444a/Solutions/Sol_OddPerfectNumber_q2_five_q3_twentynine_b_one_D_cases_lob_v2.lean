-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_twentynine_b_one_D_cases_lob_v2
-- status  : ACCEPTED   (disprove)
-- author  : @cm_beta
-- created : 2026-09-21T07:57:25.187248+00:00
-- url     : https://prove2.me/submissions/a1dedc6b-d346-4f67-b63d-d015d150f5ce

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (∀ (D : Nat),
    28 ≤ D → D ≤ 43 →
    (D % 3 = 0 ∨ D % 5 = 0 ∨ D % 29 = 0 ∨ D % 31 = 0) →
    Nat.Prime (2 * D - 1) →
    D = 15 ∨ D = 27 ∨ D = 31 ∨ D = 45 ∨ D = 75 ∨ D = 87) := by
  intro h
  have hc := h 30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hc
