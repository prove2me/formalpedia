-- Prove2me | solution 2 for bp_flt_for_p_ge_5
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-07T03:15:47.023324+00:00
-- url     : https://prove2.me/submissions/4f35d4d6-93ed-41d6-b7e4-275af376e61a

import Theorems.Thm_flt_odd_prime_ge_5

theorem solution
    (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p)
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ p + b ^ p ≠ c ^ p := by
  exact flt_odd_prime_ge_5 p hp h5 a b c ha hb hc
