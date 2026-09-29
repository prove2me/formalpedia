-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_D225_p_dvd_sigma_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T14:35:24.233323+00:00
-- url     : https://prove2.me/submissions/95e9bd5c-8e1d-4be1-9c15-0acdc516f466

import Mathlib

theorem solution (m D p sigma : Nat)
    (hrel : D * sigma = p * m ^ 2)
    (hp_eq : p = 2 * D - 1) (hp : p.Prime)
    (hD : D = 225) :
    p ∣ sigma := by
  subst hD
  have hp449 : p = 449 := by omega
  subst hp449
  have hcop : Nat.Coprime 449 225 := by norm_num
  have hdvd : (449 : Nat) ∣ 225 * sigma := ⟨m ^ 2, hrel⟩
  exact Nat.Coprime.dvd_of_dvd_mul_left hcop hdvd
