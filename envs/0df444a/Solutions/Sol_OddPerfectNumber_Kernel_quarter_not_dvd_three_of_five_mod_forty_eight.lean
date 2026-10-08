-- Prove2me | solution 1 for OddPerfectNumber.Kernel.quarter_not_dvd_three_of_five_mod_forty_eight
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T23:20:59.495979+00:00
-- url     : https://prove2.me/submissions/9fb4d14d-e374-4244-8f53-08da1c1bf2be

import Mathlib

theorem solution (p : Nat)
    (h48 : p % 48 = 5) :
    Not (Dvd.dvd 3 ((p - 1) / 4)) := by
  intro hd
  omega
