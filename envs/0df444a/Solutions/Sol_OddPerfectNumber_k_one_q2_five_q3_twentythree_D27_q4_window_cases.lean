-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_D27_q4_window_cases
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T14:06:38.205348+00:00
-- url     : https://prove2.me/submissions/d41c4b20-e006-4691-be3a-4ab2cb74d358

import Mathlib

theorem solution (q4 : Nat) (hq4prime : q4.Prime) (hlo : 691 ≤ q4) (hhi : q4 ≤ 717) :
    q4 = 691 ∨ q4 = 701 ∨ q4 = 709 := by
  interval_cases q4 <;> norm_num at hq4prime <;> norm_num
