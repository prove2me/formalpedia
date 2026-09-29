-- Prove2me | solution 1 for OddPerfectNumber.order_five_vieta_C_eq_nine_of_q_dvd_half_successor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-19T08:34:48.913955+00:00
-- url     : https://prove2.me/submissions/c8f9e7de-51e1-4675-a0f9-e28b48e951ba

import Mathlib
import Theorems.Thm_OddPerfectNumber_order_five_vieta_quotient
import Theorems.Thm_OddPerfectNumber_vieta_phi5_C_eq_three_or_nine
import Theorems.Thm_OddPerfectNumber_q_mod_four_eq_one_of_q_dvd_half_successor
import Theorems.Thm_OddPerfectNumber_vieta_C_three_impossible_of_euler_mod_four

open OddPerfectNumber

theorem solution (p q : Nat)
    (hp : p.Prime)
    (hp4 : p % 4 = 1)
    (hq : q.Prime)
    (hsqP : IsSquare (p : ZMod q))
    (hqt : q ∣ (p + 1) / 2)
    (h5 : orderOf (q : ZMod p) = 5) :
    ∃ k C : Nat,
      p + 1 = q * k
      ∧ q ^ 2 + q + k ^ 2 + k + 1 = C * (q * k - 1)
      ∧ C = 9 := by
  have h2t : 2 * ((p + 1) / 2) = p + 1 := by
    omega
  have hqplus : q ∣ p + 1 := by
    rcases hqt with ⟨r, hr⟩
    refine ⟨2 * r, ?_⟩
    rw [← h2t, hr]
    ring
  rcases hqplus with ⟨k, hk⟩
  have hqpos : 0 < q := hq.pos
  have hkpos : 0 < k := by
    nlinarith [hp.two_le, hq.two_le, hk]
  rcases order_five_vieta_quotient p q k hp hk h5 with ⟨C, hCEq, hCpos⟩
  have hclass : C = 3 ∨ C = 9 :=
    vieta_phi5_C_eq_three_or_nine q k C hqpos hkpos hCEq
  have hq4 : q % 4 = 1 :=
    q_mod_four_eq_one_of_q_dvd_half_successor p q hp4 hq hsqP hqt
  rcases hclass with hC3 | hC9
  · exfalso
    apply vieta_C_three_impossible_of_euler_mod_four p q k hp4 hq4 hk
    simpa [hC3] using hCEq
  · exact ⟨k, C, hk, hCEq, hC9⟩
