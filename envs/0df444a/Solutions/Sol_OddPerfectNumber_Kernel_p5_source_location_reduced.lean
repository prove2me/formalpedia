-- Prove2me | solution 1 for OddPerfectNumber.Kernel.p5_source_location_reduced
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T10:02:21.396862+00:00
-- url     : https://prove2.me/submissions/2fba9e1f-c0cb-4740-b220-0604c8c8060f

import Mathlib

theorem solution (d1 t : Nat)
    (ht : t.Prime) (htm : t ∣ 651 * d1)
    (ht3 : t ≠ 3) (ht7 : t ≠ 7) :
    t = 31 ∨ t ∣ d1 := by
  rcases ht.dvd_mul.mp htm with h651 | hd1
  · have hfac : 651 = 3 * (7 * 31) := by norm_num
    rw [hfac] at h651
    rcases ht.dvd_mul.mp h651 with h3 | h731
    · exact False.elim (ht3 ((Nat.prime_dvd_prime_iff_eq ht (by norm_num)).mp h3))
    · rcases ht.dvd_mul.mp h731 with h7 | h31
      · exact False.elim (ht7 ((Nat.prime_dvd_prime_iff_eq ht (by norm_num)).mp h7))
      · have hEq : t = 31 :=
          (Nat.prime_dvd_prime_iff_eq ht (by norm_num : Nat.Prime 31)).mp h31
        exact Or.inl hEq
  · exact Or.inr hd1
