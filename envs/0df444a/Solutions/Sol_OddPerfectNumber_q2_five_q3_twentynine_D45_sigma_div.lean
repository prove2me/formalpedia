-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_twentynine_D45_sigma_div
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T22:45:47.647023+00:00
-- url     : https://prove2.me/submissions/b92c97bb-89b9-4c86-8c61-cadabf29eaa8

import Mathlib

theorem solution (m D p sigma : Nat)
    (hrel : D * sigma = p * m ^ 2)
    (hD : D = 45) (hp_eq : p = 2 * D - 1) :
    89 ∣ sigma := by
  have hp : Nat.Prime p := by
    rw [hp_eq, hD]
    norm_num
  have hpd : p ∣ D * sigma := by
    rw [hrel]
    simpa [Nat.mul_comm] using (dvd_mul_left p (m ^ 2))
  have hcop : Nat.Coprime p D := by
    rw [hp_eq, hD]
    norm_num
  have hs : p ∣ sigma := hcop.dvd_of_dvd_mul_left hpd
  simpa [hp_eq, hD] using hs
