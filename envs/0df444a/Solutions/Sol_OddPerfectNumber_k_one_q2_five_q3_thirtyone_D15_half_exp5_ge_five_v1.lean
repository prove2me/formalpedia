-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirtyone_D15_half_exp5_ge_five_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T14:55:51.511618+00:00
-- url     : https://prove2.me/submissions/4012c2d1-a253-4844-b4c0-2ce0e469f449

import Mathlib

theorem solution (b : Nat) (hb : 0 < b) (hb1 : b ≠ 1) (hb2 : b ≠ 2) (hb3 : b ≠ 3) (hb4 : b ≠ 4) : 5 ≤ b := by omega
