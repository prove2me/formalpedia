-- Prove2me | solution 1 for OddPerfectNumber.orderOf_three_eq_prime_index
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-19T20:52:21.62898+00:00
-- url     : https://prove2.me/submissions/9a32f0a2-a1e3-49fe-8b29-2ef4bd3ba227

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_dvd_implies_zmod_pow_eq_one

open OddPerfectNumber

theorem solution (q4 e : Nat)
    (hq4 : q4.Prime) (hq4ne2 : q4 ≠ 2)
    (hprime : (2 * e + 1).Prime)
    (hdiv : q4 ∣ ∑ i ∈ Finset.range (2 * e + 1), 3 ^ i) :
    orderOf (3 : ZMod q4) = 2 * e + 1 := by
  have hp : (3 : ZMod q4) ^ (2 * e + 1) = 1 :=
    geom_sum_dvd_implies_zmod_pow_eq_one hdiv
  have hne : (3 : ZMod q4) ≠ 1 := by
    intro h3
    have h2 : (2 : ZMod q4) = 0 := by
      have h31 : (3 : ZMod q4) = 1 := h3
      have hsub : (3 : ZMod q4) - 1 = 0 := sub_eq_zero.mpr h31
      have hcast : (3 : ZMod q4) - 1 = 2 := by norm_num
      rw [hcast] at hsub
      exact hsub
    have hdvd : q4 ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q4).mp h2
    obtain ⟨c, hc⟩ := hdvd
    have hcpos : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h0 | hpos
      · rw [h0, Nat.mul_zero] at hc
        omega
      · exact hpos
    have hq4le : q4 ≤ q4 * c := Nat.le_mul_of_pos_right q4 hcpos
    have h2le : 2 ≤ q4 := hq4.two_le
    omega
  letI : Fact ((2 * e + 1).Prime) := ⟨hprime⟩
  exact orderOf_eq_prime hp hne
