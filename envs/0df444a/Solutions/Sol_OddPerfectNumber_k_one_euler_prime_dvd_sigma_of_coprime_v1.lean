-- Prove2me | solution 1 for OddPerfectNumber.k_one_euler_prime_dvd_sigma_of_coprime_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T14:47:13.96372+00:00
-- url     : https://prove2.me/submissions/6d7138a1-5776-4744-9411-8e863a4ae36c

import Mathlib

theorem solution (m D p sigma : Nat)
    (hrel : D * sigma = p * m ^ 2)
    (hp_eq : p = 2 * D - 1) (hp : p.Prime)
    (hD : 1 < D) :
    p ∣ sigma := by
  have hdp : D < p := by omega
  have hDpos : 0 < D := by omega
  have hndvd : ¬ p ∣ D := by
    intro h
    have hle := Nat.le_of_dvd hDpos h
    omega
  have hcop : Nat.Coprime p D := (hp.coprime_iff_not_dvd).mpr hndvd
  have hdvd : p ∣ D * sigma := ⟨m ^ 2, hrel⟩
  exact Nat.Coprime.dvd_of_dvd_mul_left hcop hdvd
