-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_D57_q4_587_absurd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T20:27:42.096863+00:00
-- url     : https://prove2.me/submissions/c0d401a4-2272-4e65-8966-d346102086a6

import Mathlib
import Theorems.Thm_OddPerfectNumber_even_order_three_mod_113
import Theorems.Thm_OddPerfectNumber_even_order_five_mod_113
import Theorems.Thm_OddPerfectNumber_even_order_nineteen_mod_113
import Theorems.Thm_OddPerfectNumber_order_q4_587_mod_113_eq_56
import Theorems.Thm_OddPerfectNumber_k_one_p113_no_local_sigma_source_general

theorem solution (sigma a b c e : Nat)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2 * c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2 * e + 1), 587 ^ i))
    (hdiv : 113 ∣ sigma) :
    False := by
  have even_not_dvd_odd : ∀ (n t : Nat), Even n → ¬ n ∣ 2 * t + 1 := by
    intro n t hn hnd
    rcases hn with ⟨k, hk⟩
    rcases hnd with ⟨u, hu⟩
    have hu' : 2 * t + 1 = (k + k) * u := by simpa [hk] using hu
    have hu'' : 2 * t + 1 = 2 * (k * u) := by
      calc
        2 * t + 1 = (k + k) * u := hu'
        _ = 2 * (k * u) := by ring
    omega
  have h3 : ¬ orderOf (3 : ZMod 113) ∣ 2 * a + 1 :=
    even_not_dvd_odd _ _ OddPerfectNumber.even_order_three_mod_113
  have h5 : ¬ orderOf (5 : ZMod 113) ∣ 2 * b + 1 :=
    even_not_dvd_odd _ _ OddPerfectNumber.even_order_five_mod_113
  have h19 : ¬ orderOf (19 : ZMod 113) ∣ 2 * c + 1 :=
    even_not_dvd_odd _ _ OddPerfectNumber.even_order_nineteen_mod_113
  have hq4 : ¬ orderOf (587 : ZMod 113) ∣ 2 * e + 1 := by
    rw [OddPerfectNumber.order_q4_587_mod_113_eq_56]
    exact even_not_dvd_odd _ _ ⟨28, by omega⟩
  exact OddPerfectNumber.k_one_p113_no_local_sigma_source_general
    sigma a b c e 587 hsigma hdiv h3 h5 h19 hq4
