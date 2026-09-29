-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_b_one_D31_q4_31_absurd_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T05:33:33.70406+00:00
-- url     : https://prove2.me/submissions/9f31d716-f5b9-45b9-8a92-1dea25fb1e16

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D31_absurd_v2

open OddPerfectNumber

theorem solution (D p sigma m a b c e q4 : Nat)
    (hrel : D * sigma = p * m ^ 2) (hD : D = 31) (hp_eq : p = 2 * D - 1)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hq4eq : q4 = 31) :
    False := by
  subst hD
  subst hq4eq
  have hp61 : p = 61 := by omega
  subst hp61
  have hpP : Nat.Prime 61 := by norm_num
  have h31 : Nat.Prime 31 := by norm_num
  have hsup : ∀ r, r.Prime → r ∣ 31 → r = 3 ∨ r = 5 ∨ r = 29 ∨ r = 31 := by
    intro r hr hrdvd
    have hr31 : r = 31 := by
      rcases (Nat.dvd_prime h31).mp hrdvd with h | h
      · exact absurd h hr.ne_one
      · exact h
    rw [hr31]
    norm_num
  exact k_one_q2_five_q3_twentynine_D31_absurd_v2 m a b c e 31 61 31 sigma
    hsigma hrel rfl rfl hpP hsup h31
