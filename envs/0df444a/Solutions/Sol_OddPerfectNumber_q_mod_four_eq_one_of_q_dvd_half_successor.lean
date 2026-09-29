-- Prove2me | solution 1 for OddPerfectNumber.q_mod_four_eq_one_of_q_dvd_half_successor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-19T00:53:50.254368+00:00
-- url     : https://prove2.me/submissions/28cc1c24-1eb7-45cd-b140-7817622f32fc

import Mathlib
import Theorems.Thm_ZMod_prime_dvd_eq_two_or_mod_four_eq_one_of_sq_add_one_eq_zero

theorem solution (p q : Nat)
    (hp4 : p % 4 = 1)
    (hq : q.Prime)
    (hsqP : IsSquare (p : ZMod q))
    (hqt : q ∣ (p + 1) / 2) :
    q % 4 = 1 := by
  have ht2 : 2 * ((p + 1) / 2) = p + 1 := by omega
  have hqt_copy := hqt
  obtain ⟨t, ht⟩ := hqt
  have hqdvd : q ∣ p + 1 := by
    rw [← ht2, ht]
    exact ⟨2 * t, by ring⟩
  have hcast : ((p + 1 : Nat) : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff (p + 1) q).mpr hqdvd
  push_cast at hcast
  have hpZ : (p : ZMod q) = -1 := by linear_combination hcast
  have hsq : IsSquare (-1 : ZMod q) := hpZ ▸ hsqP
  obtain ⟨r, hr⟩ := hsq
  have hr2 : r ^ 2 = -1 := by rw [pow_two, ← hr]
  have hx : r ^ 2 + 1 = 0 := by linear_combination hr2
  have hdisj :=
    ZMod.prime_dvd_eq_two_or_mod_four_eq_one_of_sq_add_one_eq_zero r hx hq dvd_rfl
  have hodd : ((p + 1) / 2) % 2 = 1 := by omega
  have hq2 : q ≠ 2 := by
    intro h2
    rw [h2] at hqt_copy
    omega
  rcases hdisj with h_eq2 | h_mod
  · exact absurd h_eq2 hq2
  · exact h_mod
