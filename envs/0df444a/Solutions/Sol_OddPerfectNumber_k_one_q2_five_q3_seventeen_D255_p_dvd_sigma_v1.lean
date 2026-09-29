-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_D255_p_dvd_sigma_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T14:39:53.045633+00:00
-- url     : https://prove2.me/submissions/b1530fb9-b972-44f6-8724-32946cf912aa

import Mathlib

theorem solution (m D p sigma : Nat)
    (hrel : D * sigma = p * m ^ 2)
    (hp_eq : p = 2 * D - 1) (hp : p.Prime)
    (hD : D = 255) :
    p ∣ sigma := by
  subst hD
  have hp509 : p = 509 := by omega
  subst hp509
  have hcop : Nat.Coprime 509 255 := by norm_num
  have hdvd : (509 : Nat) ∣ 255 * sigma := ⟨m ^ 2, hrel⟩
  exact Nat.Coprime.dvd_of_dvd_mul_left hcop hdvd
