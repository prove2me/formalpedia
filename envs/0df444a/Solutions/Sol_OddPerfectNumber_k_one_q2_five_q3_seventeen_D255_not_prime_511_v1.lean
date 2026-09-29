-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_D255_not_prime_511_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T13:38:52.339983+00:00
-- url     : https://prove2.me/submissions/4412de8a-967c-4eb6-9724-e0e990d6d720

import Mathlib

theorem solution : ¬ Nat.Prime (511 : Nat) := by norm_num
