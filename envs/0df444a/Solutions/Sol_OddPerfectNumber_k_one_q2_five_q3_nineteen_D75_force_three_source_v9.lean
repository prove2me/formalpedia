-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_D75_force_three_source_v9
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T00:20:57.070343+00:00
-- url     : https://prove2.me/submissions/891e3842-0010-4559-8aeb-5081690b4a7a

import Mathlib
import Theorems.Thm_OddPerfectNumber_order_three_mod_263_eq_131
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_even_order
import Theorems.Thm_OddPerfectNumber_local_sum_mod_self

theorem solution (sigma a b c e : Nat)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2 * c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2 * e + 1), 263 ^ i))
    (hdiv : 263 ∣ sigma) :
    130 ≤ 2 * a := by
  have hp263 : Nat.Prime 263 := by norm_num
  have h5ord : orderOf (5 : ZMod 263) = 262 := by
    letI : Fact (Nat.Prime 263) := ⟨by norm_num⟩
    have hne0 : (5 : ZMod 263) ≠ 0 := by
      intro hz
      have hmod := (ZMod.natCast_eq_natCast_iff' 5 0 263).mp hz
      norm_num at hmod
    apply orderOf_eq_of_pow_and_pow_div_prime (x := (5 : ZMod 263)) (n := 262) (by norm_num)
    · exact ZMod.pow_card_sub_one_eq_one hne0
    · intro r hr hrd
      have hfactor : (262 : Nat) = 2 * 131 := by norm_num
      rw [hfactor] at hrd
      rcases (Nat.Prime.dvd_mul hr).mp hrd with h2 | h131
      · have hr2 : r ∣ 2 := by simpa using h2
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hr2 with h1 | h2'
        · have hrge : 2 ≤ r := hr.two_le
          omega
        · have hr_eq : r = 2 := by omega
          subst r
          have hpow : (5 : ZMod 263) ^ 131 ≠ 1 := by
            set_option maxRecDepth 100000 in decide +revert
          simpa only [show (262 : Nat) / 2 = 131 by norm_num] using hpow
      · have hre : r = 131 :=
          (Nat.prime_dvd_prime_iff_eq hr (by norm_num : Nat.Prime 131)).mp h131
        subst r
        have hpow : (5 : ZMod 263) ^ 2 ≠ 1 := by
          set_option maxRecDepth 100000 in decide +revert
        simpa only [show (262 : Nat) / 131 = 2 by norm_num] using hpow
  have h19ord : orderOf (19 : ZMod 263) = 262 := by
    letI : Fact (Nat.Prime 263) := ⟨by norm_num⟩
    have hne0 : (19 : ZMod 263) ≠ 0 := by
      intro hz
      have hmod := (ZMod.natCast_eq_natCast_iff' 19 0 263).mp hz
      norm_num at hmod
    apply orderOf_eq_of_pow_and_pow_div_prime (x := (19 : ZMod 263)) (n := 262) (by norm_num)
    · exact ZMod.pow_card_sub_one_eq_one hne0
    · intro r hr hrd
      have hfactor : (262 : Nat) = 2 * 131 := by norm_num
      rw [hfactor] at hrd
      rcases (Nat.Prime.dvd_mul hr).mp hrd with h2 | h131
      · have hr2 : r ∣ 2 := by simpa using h2
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hr2 with h1 | h2'
        · have hrge : 2 ≤ r := hr.two_le
          omega
        · have hr_eq : r = 2 := by omega
          subst r
          have hpow : (19 : ZMod 263) ^ 131 ≠ 1 := by
            set_option maxRecDepth 100000 in decide +revert
          simpa only [show (262 : Nat) / 2 = 131 by norm_num] using hpow
      · have hre : r = 131 :=
          (Nat.prime_dvd_prime_iff_eq hr (by norm_num : Nat.Prime 131)).mp h131
        subst r
        have hpow : (19 : ZMod 263) ^ 2 ≠ 1 := by
          set_option maxRecDepth 100000 in decide +revert
        simpa only [show (262 : Nat) / 131 = 2 by norm_num] using hpow
  have h5even : Even (orderOf (5 : ZMod 263)) := by
    rw [h5ord]
    norm_num
  have h19even : Even (orderOf (19 : ZMod 263)) := by
    rw [h19ord]
    norm_num
  have hnot5 : ¬ 263 ∣ ∑ i ∈ Finset.range (2 * b + 1), 5 ^ i :=
    OddPerfectNumber.geom_sum_not_dvd_of_even_order h5even
  have hnot19 : ¬ 263 ∣ ∑ i ∈ Finset.range (2 * c + 1), 19 ^ i :=
    OddPerfectNumber.geom_sum_not_dvd_of_even_order h19even
  have hnot263 : ¬ 263 ∣ ∑ i ∈ Finset.range (2 * e + 1), 263 ^ i := by
    intro h
    have hz := Nat.dvd_iff_mod_eq_zero.mp h
    have hone := OddPerfectNumber.local_sum_mod_self 263 e hp263
    omega
  have hprod : 263 ∣
      (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2 * c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2 * e + 1), 263 ^ i) := by
    simpa [hsigma] using hdiv
  rcases hp263.dvd_mul.mp hprod with hrest | h263
  · rcases hp263.dvd_mul.mp hrest with hrest' | h19
    · rcases hp263.dvd_mul.mp hrest' with h3 | h5
      · have horder := OddPerfectNumber.geom_sum_dvd_implies_order_dvd h3
        change orderOf (3 : ZMod 263) ∣ 2 * a + 1 at horder
        rw [OddPerfectNumber.order_three_mod_263_eq_131] at horder
        rcases horder with ⟨k, hk⟩
        have hkpos : 1 ≤ k := by omega
        omega
      · exact False.elim (hnot5 h5)
    · exact False.elim (hnot19 h19)
  · exact False.elim (hnot263 h263)
