-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_D3_absurd_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T10:07:06.17113+00:00
-- url     : https://prove2.me/submissions/27573e4c-3163-4716-9713-1aba6878e48c

import Mathlib

theorem solution (D p m : Nat)
    (hD : D = 3) (hp_eq : p = 2 * D - 1)
    (h5mem : 5 ∈ m.primeFactors)
    (hpm : ¬ p ∣ m) :
    False := by
  have hp5 : p = 5 := by omega
  subst hp5
  exact hpm (Nat.dvd_of_mem_primeFactors h5mem)
