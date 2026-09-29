-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirtyone_D15_half_exp3_ge_five_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T13:51:42.748236+00:00
-- url     : https://prove2.me/submissions/16c30d31-e304-4fb2-b2b1-1cf055d1bec4

import Mathlib

theorem solution (a : Nat) (ha : 0 < a) (ha1 : a ≠ 1) (ha2 : a ≠ 2) (ha3 : a ≠ 3) (ha4 : a ≠ 4) : 5 ≤ a := by omega
