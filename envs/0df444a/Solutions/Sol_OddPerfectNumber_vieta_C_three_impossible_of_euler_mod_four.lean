-- Prove2me | solution 1 for OddPerfectNumber.vieta_C_three_impossible_of_euler_mod_four
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-19T00:53:32.571308+00:00
-- url     : https://prove2.me/submissions/c0340a26-405e-4bdf-822d-33f2015a433d

import Mathlib

theorem solution (p q k : Nat)
    (hp4 : p % 4 = 1)
    (hq4 : q % 4 = 1)
    (hpk : p + 1 = q * k)
    (heq : q ^ 2 + q + k ^ 2 + k + 1 = 3 * (q * k - 1)) :
    False := by
  have hqk_sub : q * k - 1 = p := by omega
  rw [hqk_sub] at heq
  have hqk4 : (q * k) % 4 = 2 := by omega
  have hmul := Nat.mul_mod q k 4
  rw [hq4] at hmul
  have hkm : k % 4 = 2 := by omega
  have hq2 : (q ^ 2) % 4 = 1 := by
    have hpm := Nat.pow_mod q 2 4
    rw [hq4] at hpm
    omega
  have hk2 : (k ^ 2) % 4 = 0 := by
    have hpm := Nat.pow_mod k 2 4
    rw [hkm] at hpm
    omega
  omega
