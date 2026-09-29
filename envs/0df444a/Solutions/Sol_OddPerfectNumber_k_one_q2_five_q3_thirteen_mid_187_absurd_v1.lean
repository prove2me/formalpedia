-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirteen_mid_187_absurd_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T00:23:17.991165+00:00
-- url     : https://prove2.me/submissions/d45112e4-03a4-4b16-98c4-f3d39457ced0

import Mathlib

theorem solution (m D q4 : Nat)
    (hm : Odd m)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 13 ∨ x = q4)
    (hDm : D ∣ m ^ 2)
    (hD : D = 187) (hq4 : q4 = 17) :
    False := by
  obtain ⟨k, hk⟩ := hm
  have hm0 : m ≠ 0 := by omega
  obtain ⟨t, ht⟩ := hDm
  subst hD
  subst hq4
  have h11sq : 11 ∣ m ^ 2 := ⟨17 * t, by omega⟩
  have h11m : 11 ∣ m := (by norm_num : Nat.Prime 11).dvd_of_dvd_pow h11sq
  have h11mem : 11 ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨by norm_num, h11m, hm0⟩
  have h11or := hsupport 11 h11mem
  omega
