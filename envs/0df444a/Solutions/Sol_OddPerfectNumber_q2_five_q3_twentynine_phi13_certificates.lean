-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_twentynine_phi13_certificates
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T06:39:55.965598+00:00
-- url     : https://prove2.me/submissions/6a89e13a-2478-4c93-a444-6df21ca181a3

import Mathlib

theorem solution :
    2237 ∣ ∑ i ∈ Finset.range 13, 47 ^ i ∧
      79 ∣ ∑ i ∈ Finset.range 13, 89 ^ i := by
  norm_num
