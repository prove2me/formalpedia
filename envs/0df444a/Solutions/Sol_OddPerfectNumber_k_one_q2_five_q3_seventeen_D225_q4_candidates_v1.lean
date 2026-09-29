-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_D225_q4_candidates_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-19T22:16:44.793425+00:00
-- url     : https://prove2.me/submissions/a42cbe5d-4159-4f26-8a87-e6ff732b0bd3

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_even_order

open OddPerfectNumber

-- `OddPerfectNumber.k_one_q2_five_q3_seventeen_D225_q4_candidates_v1`
--
-- Half-exponent four-support configuration `m^2 = 3^(2a) * 5^(2b) * 17^(2c) * q4^(2e)`
-- with `D = 225` (so `p = 2 * D - 1 = 449`) and the Euler relation
-- `D * sigma = p * m^2`.  Two independent ingredients pin `q4`:
--
--  * `17 | q4 - 1`: `17 | m^2`, and `17` does not divide `D = 225`, so `17 | sigma`;
--    the three non-`q4` local factors are not divisible by `17`, hence `17 | S_q4(2e)`;
--    the base `q4` is nonzero in `ZMod 17` with `q4^(2e+1) = 1`, and `2e+1` is odd,
--    so the order of `q4` in `(ZMod 17)^*` divides `gcd (2e+1) 16 = 1`, giving
--    `q4 % 17 = 1`.
--
--  * `q4 <= 592`: multiplying the four strict factor inequalities
--    `S_r(2n) * (r - 1) < r^(2n+1)`, using the Euler relation to cancel `m^2`,
--    yields `128 * (q4 - 1) * 449 < 225 * 255 * q4`, i.e. `97 * q4 < 57472`.
--
-- The primes `q4 > 17` with `q4 % 17 = 1` and `q4 <= 592` are exactly
-- `103, 137, 239, 307, 409, 443`.

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 17 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 17 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hp_eq : p = 2 * D - 1) (hp : p.Prime)
    (hq4 : q4.Prime) (hq4gt : 17 < q4)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (he : 1 ≤ e)
    (hD : D = 225) :
    q4 = 103 ∨ q4 = 137 ∨ q4 = 239 ∨ q4 = 307 ∨ q4 = 409 ∨ q4 = 443 := by
  subst hD
  have hp449 : p = 449 := by omega
  subst hp449
  have hq4pos : 1 ≤ q4 := by omega
  -- 17 divides m^2
  have h17m : 17 ∣ m ^ 2 := by
    rw [hfac]
    exact dvd_trans (dvd_pow_self 17 (n := 2*c) (by omega))
      ⟨3 ^ (2*a) * 5 ^ (2*b) * q4 ^ (2*e), by ring⟩
  -- 17 divides sigma
  have h17sig : 17 ∣ sigma := by
    have hmul : 17 ∣ 225 * sigma := by
      rw [hrel]
      exact dvd_mul_of_dvd_right h17m 449
    have hD17 : ¬ 17 ∣ (225 : ℕ) := by norm_num
    rcases ((by norm_num : Nat.Prime 17).dvd_mul.mp hmul) with h | h
    · exact absurd h hD17
    · exact h
  -- the three non-q4 local factors are not divisible by 17
  have h17ne3 : ¬ 17 ∣ ∑ i ∈ Finset.range (2*a + 1), 3 ^ i := by
    apply geom_sum_not_dvd_of_even_order
    have hnot : ¬ ((3 : ℕ) : ZMod 17) ^ 2 ^ 3 = 1 := by decide
    have hfin : ((3 : ℕ) : ZMod 17) ^ 2 ^ (3 + 1) = 1 := by decide
    have hord : orderOf ((3 : ℕ) : ZMod 17) = 16 := by
      have h := orderOf_eq_prime_pow (p := 2) hnot hfin
      simpa using h
    rw [hord]
    exact ⟨8, by norm_num⟩
  have h17ne5 : ¬ 17 ∣ ∑ i ∈ Finset.range (2*b + 1), 5 ^ i := by
    apply geom_sum_not_dvd_of_even_order
    have hnot : ¬ ((5 : ℕ) : ZMod 17) ^ 2 ^ 3 = 1 := by decide
    have hfin : ((5 : ℕ) : ZMod 17) ^ 2 ^ (3 + 1) = 1 := by decide
    have hord : orderOf ((5 : ℕ) : ZMod 17) = 16 := by
      have h := orderOf_eq_prime_pow (p := 2) hnot hfin
      simpa using h
    rw [hord]
    exact ⟨8, by norm_num⟩
  have h17ne17 : ¬ 17 ∣ ∑ i ∈ Finset.range (2*c + 1), 17 ^ i := by
    intro hd
    have htail : 17 ∣ ∑ i ∈ Finset.range (2*c), 17 ^ (i+1) := by
      apply Finset.dvd_sum
      intro i _
      exact dvd_pow_self 17 (n := i+1) (by omega)
    have hsplit : (∑ i ∈ Finset.range (2*c + 1), 17 ^ i) =
        (∑ i ∈ Finset.range (2*c), 17 ^ (i+1)) + 1 := by
      rw [Finset.sum_range_succ']
      simp
    rw [hsplit] at hd
    have h1 : 17 ∣ 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hd' := Nat.mod_eq_zero_of_dvd hd
      have ht' := Nat.mod_eq_zero_of_dvd htail
      omega
    norm_num at h1
  -- hence the q4 local factor is divisible by 17
  have h17S : 17 ∣ ∑ i ∈ Finset.range (2*e + 1), q4 ^ i := by
    rw [hsigma] at h17sig
    rcases ((by norm_num : Nat.Prime 17).dvd_mul.mp h17sig) with h | h
    · rcases ((by norm_num : Nat.Prime 17).dvd_mul.mp h) with h | h
      · rcases ((by norm_num : Nat.Prime 17).dvd_mul.mp h) with h | h
        · exact absurd h h17ne3
        · exact absurd h h17ne5
      · exact absurd h h17ne17
    · exact h
  -- transfer to a ZMod 17 power relation
  have hgeom := geom_mul_sub_one q4 (2*e + 1) hq4pos
  have h17dvd : 17 ∣ q4 ^ (2*e + 1) - 1 := by
    rw [← hgeom]
    exact dvd_mul_of_dvd_left h17S _
  have hmod : (q4 : ZMod 17) ^ (2*e + 1) = 1 := by
    have hpow1 : 1 ≤ q4 ^ (2*e + 1) := Nat.one_le_pow _ _ hq4pos
    have hzero : ((q4 ^ (2*e + 1) - 1 : Nat) : ZMod 17) = 0 :=
      (ZMod.natCast_eq_zero_iff (q4 ^ (2*e + 1) - 1) 17).mpr h17dvd
    have hcast : ((q4 ^ (2*e + 1) - 1 : Nat) : ZMod 17) =
        (q4 : ZMod 17) ^ (2*e + 1) - 1 := by
      rw [Nat.cast_sub hpow1, Nat.cast_pow, Nat.cast_one]
    rw [hcast] at hzero
    exact sub_eq_zero.mp hzero
  -- the order of q4 in (ZMod 17)^* is odd and divides 16, hence is 1
  have h17ndvdq4 : ¬ 17 ∣ q4 := by
    intro hd
    have h := hq4.eq_one_or_self_of_dvd 17 hd
    rcases h with h | h <;> omega
  have hq4ne0 : (q4 : ZMod 17) ≠ 0 := by
    intro h0
    exact h17ndvdq4 ((ZMod.natCast_eq_zero_iff q4 17).mp h0)
  have hdvd16 : orderOf ((q4 : ℕ) : ZMod 17) ∣ 16 := by
    haveI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
    have hf : ((q4 : ℕ) : ZMod 17) ^ (17 - 1) = 1 :=
      ZMod.pow_card_sub_one_eq_one hq4ne0
    simpa using (orderOf_dvd_iff_pow_eq_one.mpr hf)
  have hdvdodd : orderOf ((q4 : ℕ) : ZMod 17) ∣ 2*e + 1 :=
    orderOf_dvd_iff_pow_eq_one.mpr hmod
  have hone : orderOf ((q4 : ℕ) : ZMod 17) = 1 := by
    have hodd : Odd (2*e + 1) := ⟨e, by ring⟩
    have h2 : Nat.Coprime 2 (2*e + 1) := Nat.coprime_two_left.mpr hodd
    have hcop : Nat.Coprime (16 : ℕ) (2*e + 1) := by
      have h := (Nat.coprime_pow_left_iff (n := 4) (by norm_num) 2 (2*e + 1)).mpr h2
      simpa using h
    exact Nat.eq_one_of_dvd_coprimes hcop hdvd16 hdvdodd
  have hdvd17 : 17 ∣ q4 - 1 := by
    have h1 : ((q4 : ℕ) : ZMod 17) = 1 := orderOf_eq_one_iff.mp hone
    have h2 : ((q4 - 1 : Nat) : ZMod 17) = 0 := by
      rw [Nat.cast_sub hq4pos, h1]
      simp
    exact (ZMod.natCast_eq_zero_iff (q4 - 1) 17).mp h2
  -- geometric-sum identities: (base - 1) * S + 1 = base^(len)
  have g3 : 2 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) + 1 = 3 ^ (2*a + 1) := by
    rw [mul_comm 2 _]
    exact geom_sum_mul_add 2 (2*a + 1)
  have g5 : 4 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) + 1 = 5 ^ (2*b + 1) := by
    rw [mul_comm 4 _]
    exact geom_sum_mul_add 4 (2*b + 1)
  have g17 : 16 * (∑ i ∈ Finset.range (2*c + 1), 17 ^ i) + 1 = 17 ^ (2*c + 1) := by
    rw [mul_comm 16 _]
    exact geom_sum_mul_add 16 (2*c + 1)
  have gq : (q4 - 1) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i) + 1 = q4 ^ (2*e + 1) := by
    have h := geom_sum_mul_add (q4 - 1) (2*e + 1)
    rw [Nat.sub_add_cancel hq4pos] at h
    rw [mul_comm (q4 - 1) _]
    exact h
  -- strict upper bounds on each factor
  have e1 : 2 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) < 3 ^ (2*a + 1) := by omega
  have e2 : 4 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) < 5 ^ (2*b + 1) := by omega
  have e3 : 16 * (∑ i ∈ Finset.range (2*c + 1), 17 ^ i) < 17 ^ (2*c + 1) := by omega
  have e4 : (q4 - 1) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i) < q4 ^ (2*e + 1) := by omega
  have l2 : 4 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) ≤ 5 ^ (2*b + 1) := by omega
  have l3 : 16 * (∑ i ∈ Finset.range (2*c + 1), 17 ^ i) ≤ 17 ^ (2*c + 1) := by omega
  have l4 : (q4 - 1) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i) ≤ q4 ^ (2*e + 1) := by omega
  have hBpos : 0 < 5 ^ (2*b + 1) := by positivity
  have hCpos : 0 < 17 ^ (2*c + 1) := by positivity
  have hEpos : 0 < q4 ^ (2*e + 1) := by positivity
  -- four-factor strict product bound
  have p1 : (2 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i)) * (4 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i))
      < 3 ^ (2*a + 1) * 5 ^ (2*b + 1) :=
    Nat.mul_lt_mul_of_lt_of_le e1 l2 hBpos
  have p2 : ((2 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i)) * (4 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i)))
        * (16 * (∑ i ∈ Finset.range (2*c + 1), 17 ^ i))
      < (3 ^ (2*a + 1) * 5 ^ (2*b + 1)) * 17 ^ (2*c + 1) :=
    Nat.mul_lt_mul_of_lt_of_le p1 l3 hCpos
  have p3 : (((2 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i)) * (4 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i)))
        * (16 * (∑ i ∈ Finset.range (2*c + 1), 17 ^ i))) * ((q4 - 1) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
      < ((3 ^ (2*a + 1) * 5 ^ (2*b + 1)) * 17 ^ (2*c + 1)) * q4 ^ (2*e + 1) :=
    Nat.mul_lt_mul_of_lt_of_le p2 l4 hEpos
  -- bridge variable exponents to factored form
  have r3 : (3 : ℕ) ^ (2*a + 1) = 3 ^ (2*a) * 3 := pow_succ 3 (2*a)
  have r5 : (5 : ℕ) ^ (2*b + 1) = 5 ^ (2*b) * 5 := pow_succ 5 (2*b)
  have r17 : (17 : ℕ) ^ (2*c + 1) = 17 ^ (2*c) * 17 := pow_succ 17 (2*c)
  have rq : q4 ^ (2*e + 1) = q4 ^ (2*e) * q4 := pow_succ q4 (2*e)
  have p3b := p3
  rw [r3, r5, r17, rq] at p3b
  -- transport to the sigma relation and cancel m^2
  have fin : 128 * (q4 - 1) * 225 * sigma < 225 * 255 * q4 * m ^ 2 := by
    rw [hsigma, hfac]
    linear_combination 225 * p3b
  have hm2 : 0 < m ^ 2 := by rw [hfac]; positivity
  have fin2 : (128 * (q4 - 1) * 449) * m ^ 2 < (225 * 255 * q4) * m ^ 2 := by
    have hrw : 128 * (q4 - 1) * 225 * sigma = (128 * (q4 - 1) * 449) * m ^ 2 := by
      linear_combination 128 * (q4 - 1) * hrel
    rw [← hrw]
    exact fin
  have fin3 : 128 * (q4 - 1) * 449 < 225 * 255 * q4 :=
    lt_of_mul_lt_mul_right fin2 (le_of_lt hm2)
  have hbound : q4 ≤ 592 := by omega
  -- finite enumeration of the congruent primes
  obtain ⟨k, hk⟩ := hdvd17
  have hkq : q4 = 17 * k + 1 := by omega
  have hk34 : k ≤ 34 := by omega
  interval_cases k <;> (rw [hkq] at hq4 ⊢) <;> first
    | decide
    | (exfalso; norm_num at hq4)
