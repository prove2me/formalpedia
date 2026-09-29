-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_D289_q4_mod5_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-19T21:42:49.767472+00:00
-- url     : https://prove2.me/submissions/0c30d92a-14c0-4455-9390-49255c3c006b

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_even_order
import Theorems.Thm_OddPerfectNumber_order_three_mod_five_eq_four

open OddPerfectNumber

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 17 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 17 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hp_eq : p = 2 * D - 1)
    (hq4gt : 17 < q4)
    (hb : 1 ≤ b)
    (hD : D = 289) :
    q4 % 5 = 1 := by
  have hq4pos : 1 ≤ q4 := by omega
  have h2b : 2 * b ≠ 0 := by omega
  -- 5 divides m^2
  have h5m : 5 ∣ m ^ 2 := by
    rw [hfac]
    exact dvd_trans (dvd_pow_self 5 (n := 2*b) h2b)
      ⟨3 ^ (2*a) * 17 ^ (2*c) * q4 ^ (2*e), by ring⟩
  -- 5 divides sigma
  have h5sig : 5 ∣ sigma := by
    have hmul : 5 ∣ D * sigma := by
      rw [hrel]
      exact dvd_mul_of_dvd_right h5m p
    have hD5 : ¬ 5 ∣ D := by rw [hD]; norm_num
    rcases (Nat.prime_five.dvd_mul.mp hmul) with h | h
    · exact absurd h hD5
    · exact h
  -- the 3, 5 and 17 local factors are not divisible by 5
  have h3ne : ¬ 5 ∣ ∑ i ∈ Finset.range (2*a + 1), 3 ^ i := by
    apply geom_sum_not_dvd_of_even_order
    have h4 : orderOf ((3 : ℕ) : ZMod 5) = 4 := by
      simpa using order_three_mod_five_eq_four
    rw [h4]
    norm_num
  have h5ne : ¬ 5 ∣ ∑ i ∈ Finset.range (2*b + 1), 5 ^ i := by
    intro hd
    have htail : 5 ∣ ∑ i ∈ Finset.range (2*b), 5 ^ (i+1) := by
      apply Finset.dvd_sum
      intro i _
      exact dvd_pow_self 5 (n := i+1) (by omega)
    have hsplit : (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) =
        (∑ i ∈ Finset.range (2*b), 5 ^ (i+1)) + 1 := by
      rw [Finset.sum_range_succ']
      simp
    rw [hsplit] at hd
    have h1 : 5 ∣ 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hd' := Nat.mod_eq_zero_of_dvd hd
      have ht' := Nat.mod_eq_zero_of_dvd htail
      omega
    norm_num at h1
  have h17ne : ¬ 5 ∣ ∑ i ∈ Finset.range (2*c + 1), 17 ^ i := by
    apply geom_sum_not_dvd_of_even_order
    have h2 : ((17 : ℕ) : ZMod 5) = ((2 : ℕ) : ZMod 5) := by decide
    rw [h2]
    have hnot : ¬ ((2 : ℕ) : ZMod 5) ^ 2 ^ 1 = 1 := by decide
    have hfin : ((2 : ℕ) : ZMod 5) ^ 2 ^ (1 + 1) = 1 := by decide
    have h4 : orderOf ((2 : ℕ) : ZMod 5) = 4 := by
      simpa using orderOf_eq_prime_pow (p := 2) hnot hfin
    rw [h4]
    norm_num
  -- hence the q4 local factor is divisible by 5
  have h5S : 5 ∣ ∑ i ∈ Finset.range (2*e + 1), q4 ^ i := by
    rw [hsigma] at h5sig
    rcases (Nat.prime_five.dvd_mul.mp h5sig) with h | h
    · rcases (Nat.prime_five.dvd_mul.mp h) with h | h
      · rcases (Nat.prime_five.dvd_mul.mp h) with h | h
        · exact absurd h h3ne
        · exact absurd h h5ne
      · exact absurd h h17ne
    · exact h
  -- 5 | S_q4(2e+1) and q4 > 17 force q4 % 5 = 1
  have hgeom := geom_mul_sub_one q4 (2*e + 1) hq4pos
  have h5dvd : 5 ∣ q4 ^ (2*e + 1) - 1 := by
    rw [← hgeom]
    exact dvd_mul_of_dvd_left h5S _
  have hmod : (q4 : ZMod 5) ^ (2*e + 1) = 1 := by
    have hpow1 : 1 ≤ q4 ^ (2*e + 1) := Nat.one_le_pow _ _ hq4pos
    have hzero : ((q4 ^ (2*e + 1) - 1 : Nat) : ZMod 5) = 0 :=
      (ZMod.natCast_eq_zero_iff (q4 ^ (2*e + 1) - 1) 5).mpr h5dvd
    have hcast : ((q4 ^ (2*e + 1) - 1 : Nat) : ZMod 5) =
        (q4 : ZMod 5) ^ (2*e + 1) - 1 := by
      rw [Nat.cast_sub hpow1, Nat.cast_pow, Nat.cast_one]
    rw [hcast] at hzero
    exact sub_eq_zero.mp hzero
  have hx : (q4 : ZMod 5) = ((q4 % 5 : ℕ) : ZMod 5) :=
    (ZMod.natCast_mod q4 5).symm
  have hodd : Odd (2*e + 1) := ⟨e, by ring⟩
  have h0bad : ((0 : ℕ) : ZMod 5) ^ (2*e + 1) ≠ 1 := by
    rw [Nat.cast_zero, zero_pow (show 2*e + 1 ≠ 0 by omega)]
    decide
  have h2bad : ((2 : ℕ) : ZMod 5) ^ (2*e + 1) ≠ 1 := by
    have hsq : ((2 : ℕ) : ZMod 5) ^ 2 = ((4 : ℕ) : ZMod 5) := by decide
    have hsplit : ((2 : ℕ) : ZMod 5) ^ (2*e + 1) =
        ((2 : ℕ) : ZMod 5) * ((4 : ℕ) : ZMod 5) ^ e := by
      rw [show 2*e + 1 = 2*e + 1 from rfl, pow_succ', pow_mul, hsq]
    rw [hsplit]
    have h4 : ((4 : ℕ) : ZMod 5) = -1 := by decide
    rw [h4]
    rcases neg_one_pow_eq_or (R := ZMod 5) e with he | he <;> rw [he] <;> decide
  have h3bad : ((3 : ℕ) : ZMod 5) ^ (2*e + 1) ≠ 1 := by
    have hsq : ((3 : ℕ) : ZMod 5) ^ 2 = ((9 : ℕ) : ZMod 5) := by decide
    have hsplit : ((3 : ℕ) : ZMod 5) ^ (2*e + 1) =
        ((3 : ℕ) : ZMod 5) * ((9 : ℕ) : ZMod 5) ^ e := by
      rw [show 2*e + 1 = 2*e + 1 from rfl, pow_succ', pow_mul, hsq]
    rw [hsplit]
    have h9 : ((9 : ℕ) : ZMod 5) = -1 := by decide
    rw [h9]
    rcases neg_one_pow_eq_or (R := ZMod 5) e with he | he <;> rw [he] <;> decide
  have h4bad : ((4 : ℕ) : ZMod 5) ^ (2*e + 1) ≠ 1 := by
    have h4 : ((4 : ℕ) : ZMod 5) = -1 := by decide
    rw [h4, hodd.neg_one_pow]
    decide
  have hcases : q4 % 5 = 0 ∨ q4 % 5 = 1 ∨ q4 % 5 = 2 ∨
      q4 % 5 = 3 ∨ q4 % 5 = 4 := by omega
  rcases hcases with h | h | h | h | h
  · exfalso
    rw [hx, h] at hmod
    exact h0bad hmod
  · exact h
  · exfalso
    rw [hx, h] at hmod
    exact h2bad hmod
  · exfalso
    rw [hx, h] at hmod
    exact h3bad hmod
  · exfalso
    rw [hx, h] at hmod
    exact h4bad hmod
