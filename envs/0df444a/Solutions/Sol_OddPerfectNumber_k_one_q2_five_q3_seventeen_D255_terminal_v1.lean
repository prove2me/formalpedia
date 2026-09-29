-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_D255_terminal_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T14:44:07.406533+00:00
-- url     : https://prove2.me/submissions/3f188aef-88e8-4dce-83b2-670a8816cd2a

import Mathlib

theorem solution (q4 : Nat)
    (hq4 : q4.Prime)
    (hcase : q4 = 511) :
    False := by
  subst hcase
  norm_num at hq4
