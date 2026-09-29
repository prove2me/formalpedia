-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_D289_p_dvd_sigma_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T14:33:22.338126+00:00
-- url     : https://prove2.me/submissions/26cc40ed-7cad-4d35-b1a9-d8c7ab462dcd

import Mathlib

theorem solution (m D p sigma : Nat)
    (hrel : D * sigma = p * m ^ 2)
    (hp_eq : p = 2 * D - 1) (hp : p.Prime)
    (hD : D = 289) :
    p ∣ sigma := by
  subst hD
  have hp577 : p = 577 := by omega
  subst hp577
  have hcop : Nat.Coprime 577 289 := by norm_num
  have hdvd : (577 : Nat) ∣ 289 * sigma := ⟨m ^ 2, hrel⟩
  exact Nat.Coprime.dvd_of_dvd_mul_left hcop hdvd
