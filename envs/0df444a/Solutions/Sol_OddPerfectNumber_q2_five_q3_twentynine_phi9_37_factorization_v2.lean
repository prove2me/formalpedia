-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_twentynine_phi9_37_factorization_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T06:44:52.56029+00:00
-- url     : https://prove2.me/submissions/e6e91074-1840-422a-9cb2-b96a452d3596

import Mathlib

theorem solution :
    37 ^ 6 + 37 ^ 3 + 1 = 3 * 73 * 127 * 92251 := by
  norm_num
