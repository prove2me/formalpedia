-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirteen_large_D_absurd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T18:20:19.028253+00:00
-- url     : https://prove2.me/submissions/99ba05c1-026c-486b-a05b-54d82cba6194

import Mathlib

theorem solution (D : Nat)
    (hDlow : 215 ≤ D) (hDupper : D ≤ 685)
    (h5pow : 390625 ∣ D) :
    False := by
  have hDpos : 0 < D := by omega
  have hle : 390625 ≤ D := Nat.le_of_dvd hDpos h5pow
  omega
