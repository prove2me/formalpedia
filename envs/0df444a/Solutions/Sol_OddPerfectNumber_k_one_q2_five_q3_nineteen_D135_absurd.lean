-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_D135_absurd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T20:53:11.722056+00:00
-- url     : https://prove2.me/submissions/d8c5587c-e1de-43e6-bf91-22e33758b8b3

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D135_no_q4_candidate

theorem solution (q4 : Nat)
    (hq4prime : q4.Prime) (hlow : 146 ≤ q4) (hhigh : q4 ≤ 148) :
    False := by
  exact OddPerfectNumber.k_one_q2_five_q3_nineteen_D135_no_q4_candidate q4 hq4prime hlow hhigh
