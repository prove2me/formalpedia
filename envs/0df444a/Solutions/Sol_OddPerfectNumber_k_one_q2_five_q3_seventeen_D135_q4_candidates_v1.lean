-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_D135_q4_candidates_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-19T23:04:35.924014+00:00
-- url     : https://prove2.me/submissions/43b41fd9-850a-40bc-bf78-48e04e3e1a9e

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_even_order
import Theorems.Thm_OddPerfectNumber_order_three_mod_five_eq_four

open OddPerfectNumber

-- `OddPerfectNumber.k_one_q2_five_q3_seventeen_D135_q4_candidates_v1`
--
-- Half-exponent four-support configuration `m^2 = 3^(2a) * 5^(2b) * 17^(2c) * q4^(2e)`
-- with `D = 135` (so `p = 2 * D - 1 = 269`) and the Euler relation
-- `D * sigma = p * m^2`.
--
-- `D = 3^3 * 5`, so two primes of `D` divide `D` and the `r` does-not-divide-`D`
-- shortcut of the `D = 225` lemma does not apply.  Cancelling one power of the
-- prime between the two sides (using `2 n_r > v_r(D)`) gives `r | sigma` for
-- `r = 3` and `r = 5`; `17 | sigma` is immediate since `17` does not divide `135`.
--
-- `r = 3` needs `a >= 2`.  This is free: `27 | 135 * sigma = 269 * m^2` and
-- `Nat.Coprime 27 269` give `27 | m^2`, and since `3` is coprime to the other
-- three support factors, `27 | 3^(2a)`, so `3 <= 2a` and `a >= 2`.
--
-- The nine non-`q4` local factors are divisible by none of `3, 5, 17` (order
-- arguments for the mixed pairs, an explicit `1 + r*(...)` tail for the self
-- factors), so each of `3, 5, 17` divides `S_q4(2e)`.  With `q4` a nonzero unit
-- modulo each of them and `2e+1` odd, the order of `q4` divides
-- `gcd (2e+1) (r-1) = 1`, so `q4 % r = 1` and `255 | q4 - 1`.
--
-- The congruence package is isolated as its own declaration so that the `omega`
-- calls below see a small local context.

set_option maxHeartbeats 1200000 in
theorem opn_d135_congruence (m a b c e q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 17 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 17 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : 135 * sigma = 269 * m ^ 2)
    (hq4 : q4.Prime) (hq4gt : 17 < q4)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (he : 1 ≤ e) :
    255 ∣ q4 - 1 := by
  have hq4pos : 1 ≤ q4 := by omega
  have h3ndvd5 : ¬ 3 ∣ (5 : ℕ) := by norm_num
  have h3ndvd17 : ¬ 3 ∣ (17 : ℕ) := by norm_num
  have h3ndvdq4 : ¬ 3 ∣ q4 := by
    intro hd
    have h := hq4.eq_one_or_self_of_dvd 3 hd
    rcases h with h | h <;> omega
  -- 27 divides m^2
  have h27m : 27 ∣ m ^ 2 := by
    have h1 : 27 ∣ 135 * sigma := by
      rw [show (135 : ℕ) = 27 * 5 by norm_num]
      exact dvd_mul_of_dvd_left (dvd_mul_right 27 5) sigma
    rw [hrel] at h1
    exact (by norm_num : Nat.Coprime 27 269).dvd_of_dvd_mul_left h1
  -- 3 is coprime to the remaining three support factors
  have hcopX : Nat.Coprime 27 (5 ^ (2*b) * 17 ^ (2*c) * q4 ^ (2*e)) := by
    have hc5 : Nat.Coprime 3 (5 ^ (2*b)) :=
      (Nat.coprime_pow_right_iff (by omega : 0 < 2*b) 3 5).mpr (by norm_num)
    have hc17 : Nat.Coprime 3 (17 ^ (2*c)) :=
      (Nat.coprime_pow_right_iff (by omega : 0 < 2*c) 3 17).mpr (by norm_num)
    have hcq : Nat.Coprime 3 (q4 ^ (2*e)) :=
      (Nat.coprime_pow_right_iff (by omega : 0 < 2*e) 3 q4).mpr
        ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 3)).mpr h3ndvdq4)
    have h3X : Nat.Coprime 3 (5 ^ (2*b) * 17 ^ (2*c) * q4 ^ (2*e)) :=
      (hc5.mul_right hc17).mul_right hcq
    have h := (Nat.coprime_pow_left_iff (n := 3) (by norm_num) 3
      (5 ^ (2*b) * 17 ^ (2*c) * q4 ^ (2*e))).mpr h3X
    simpa using h
  -- hence 27 divides 3^(2a)
  have h27_3a : 27 ∣ 3 ^ (2*a) := by
    have h : 27 ∣ 3 ^ (2*a) * (5 ^ (2*b) * 17 ^ (2*c) * q4 ^ (2*e)) := by
      have hh := h27m
      rw [hfac] at hh
      convert hh using 1
      ring
    exact hcopX.dvd_of_dvd_mul_right h
  -- so a >= 2
  have ha2 : 2 ≤ a := by
    obtain ⟨k, hk_le, hk_eq⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp h27_3a
    have hk3 : 3 ≤ k := by
      by_contra h
      have h2 : k ≤ 2 := by omega
      have hle : (3 : ℕ) ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) h2
      rw [← hk_eq] at hle
      norm_num at hle
    omega
  -- cancel 3: m^2 = 3^4 * K3
  have h3sig : 3 ∣ sigma := by
    have hm2_3 : m ^ 2 =
        81 * (3 ^ (2*a - 4) * 5 ^ (2*b) * 17 ^ (2*c) * q4 ^ (2*e)) := by
      rw [hfac]
      have h3 : (3 : ℕ) ^ (2*a) = 3 ^ 4 * 3 ^ (2*a - 4) := by
        rw [← pow_add]
        congr 1
        omega
      rw [h3]
      ring
    have h3rel : 5 * sigma =
        269 * (3 * (3 ^ (2*a - 4) * 5 ^ (2*b) * 17 ^ (2*c) * q4 ^ (2*e))) := by
      have h := hrel
      rw [hm2_3] at h
      have h' : 27 * (5 * sigma) =
          27 * (269 * (3 * (3 ^ (2*a - 4) * 5 ^ (2*b) * 17 ^ (2*c) * q4 ^ (2*e)))) := by
        nlinarith [h]
      exact Nat.mul_left_cancel (by norm_num) h'
    have hdvd : 3 ∣ 5 * sigma := by
      rw [h3rel]
      exact dvd_mul_of_dvd_right (dvd_mul_right 3 _) 269
    rcases ((by norm_num : Nat.Prime 3).dvd_mul.mp hdvd) with h | h
    · norm_num at h
    · exact h
  -- cancel 5: m^2 = 5^2 * K5
  have h5sig : 5 ∣ sigma := by
    have hm2_5 : m ^ 2 =
        25 * (3 ^ (2*a) * 5 ^ (2*b - 2) * 17 ^ (2*c) * q4 ^ (2*e)) := by
      rw [hfac]
      have h5 : (5 : ℕ) ^ (2*b) = 5 ^ 2 * 5 ^ (2*b - 2) := by
        rw [← pow_add]
        congr 1
        omega
      rw [h5]
      ring
    have h5rel : 27 * sigma =
        269 * (5 * (3 ^ (2*a) * 5 ^ (2*b - 2) * 17 ^ (2*c) * q4 ^ (2*e))) := by
      have h := hrel
      rw [hm2_5] at h
      have h' : 5 * (27 * sigma) =
          5 * (269 * (5 * (3 ^ (2*a) * 5 ^ (2*b - 2) * 17 ^ (2*c) * q4 ^ (2*e)))) := by
        nlinarith [h]
      exact Nat.mul_left_cancel (by norm_num) h'
    have hdvd : 5 ∣ 27 * sigma := by
      rw [h5rel]
      exact dvd_mul_of_dvd_right (dvd_mul_right 5 _) 269
    rcases ((by norm_num : Nat.Prime 5).dvd_mul.mp hdvd) with h | h
    · norm_num at h
    · exact h
  -- 17 divides m^2 and 17 does not divide 135
  have h17m : 17 ∣ m ^ 2 := by
    rw [hfac]
    exact dvd_trans (dvd_pow_self 17 (n := 2*c) (by omega))
      ⟨3 ^ (2*a) * 5 ^ (2*b) * q4 ^ (2*e), by ring⟩
  have h17sig : 17 ∣ sigma := by
    have hmul : 17 ∣ 135 * sigma := by
      rw [hrel]
      exact dvd_mul_of_dvd_right h17m 269
    have hD17 : ¬ 17 ∣ (135 : ℕ) := by norm_num
    rcases ((by norm_num : Nat.Prime 17).dvd_mul.mp hmul) with h | h
    · exact absurd h hD17
    · exact h
  -- the three non-q4 local factors are not divisible by 3
  have h3ne3 : ¬ 3 ∣ ∑ i ∈ Finset.range (2*a + 1), 3 ^ i := by
    intro hd
    have htail : 3 ∣ ∑ i ∈ Finset.range (2*a), 3 ^ (i+1) := by
      apply Finset.dvd_sum
      intro i _
      exact dvd_pow_self 3 (n := i+1) (by omega)
    have hsplit : (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) =
        (∑ i ∈ Finset.range (2*a), 3 ^ (i+1)) + 1 := by
      rw [Finset.sum_range_succ']
      simp
    rw [hsplit] at hd
    have h1 : 3 ∣ 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hd' := Nat.mod_eq_zero_of_dvd hd
      have ht' := Nat.mod_eq_zero_of_dvd htail
      omega
    norm_num at h1
  have h3ne5 : ¬ 3 ∣ ∑ i ∈ Finset.range (2*b + 1), 5 ^ i := by
    apply geom_sum_not_dvd_of_even_order
    have h2 : ((5 : ℕ) : ZMod 3) = ((2 : ℕ) : ZMod 3) := by decide
    rw [h2]
    have hnot : ¬ ((2 : ℕ) : ZMod 3) ^ 2 ^ 0 = 1 := by decide
    have hfin : ((2 : ℕ) : ZMod 3) ^ 2 ^ (0 + 1) = 1 := by decide
    have hord : orderOf ((2 : ℕ) : ZMod 3) = 2 := by
      have h := orderOf_eq_prime_pow (p := 2) hnot hfin
      simpa using h
    rw [hord]
    exact ⟨1, by norm_num⟩
  have h3ne17 : ¬ 3 ∣ ∑ i ∈ Finset.range (2*c + 1), 17 ^ i := by
    apply geom_sum_not_dvd_of_even_order
    have h2 : ((17 : ℕ) : ZMod 3) = ((2 : ℕ) : ZMod 3) := by decide
    rw [h2]
    have hnot : ¬ ((2 : ℕ) : ZMod 3) ^ 2 ^ 0 = 1 := by decide
    have hfin : ((2 : ℕ) : ZMod 3) ^ 2 ^ (0 + 1) = 1 := by decide
    have hord : orderOf ((2 : ℕ) : ZMod 3) = 2 := by
      have h := orderOf_eq_prime_pow (p := 2) hnot hfin
      simpa using h
    rw [hord]
    exact ⟨1, by norm_num⟩
  -- the three non-q4 local factors are not divisible by 5
  have h5ne3 : ¬ 5 ∣ ∑ i ∈ Finset.range (2*a + 1), 3 ^ i := by
    apply geom_sum_not_dvd_of_even_order
    have h4 : orderOf ((3 : ℕ) : ZMod 5) = 4 := by
      simpa using order_three_mod_five_eq_four
    rw [h4]
    exact ⟨2, by norm_num⟩
  have h5ne5 : ¬ 5 ∣ ∑ i ∈ Finset.range (2*b + 1), 5 ^ i := by
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
  have h5ne17 : ¬ 5 ∣ ∑ i ∈ Finset.range (2*c + 1), 17 ^ i := by
    apply geom_sum_not_dvd_of_even_order
    have h2 : ((17 : ℕ) : ZMod 5) = ((2 : ℕ) : ZMod 5) := by decide
    rw [h2]
    have hnot : ¬ ((2 : ℕ) : ZMod 5) ^ 2 ^ 1 = 1 := by decide
    have hfin : ((2 : ℕ) : ZMod 5) ^ 2 ^ (1 + 1) = 1 := by decide
    have hord : orderOf ((2 : ℕ) : ZMod 5) = 4 := by
      have h := orderOf_eq_prime_pow (p := 2) hnot hfin
      simpa using h
    rw [hord]
    exact ⟨2, by norm_num⟩
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
  -- hence the q4 local factor is divisible by 3, 5 and 17
  have h3S : 3 ∣ ∑ i ∈ Finset.range (2*e + 1), q4 ^ i := by
    rw [hsigma] at h3sig
    rcases ((by norm_num : Nat.Prime 3).dvd_mul.mp h3sig) with h | h
    · rcases ((by norm_num : Nat.Prime 3).dvd_mul.mp h) with h | h
      · rcases ((by norm_num : Nat.Prime 3).dvd_mul.mp h) with h | h
        · exact absurd h h3ne3
        · exact absurd h h3ne5
      · exact absurd h h3ne17
    · exact h
  have h5S : 5 ∣ ∑ i ∈ Finset.range (2*e + 1), q4 ^ i := by
    rw [hsigma] at h5sig
    rcases ((by norm_num : Nat.Prime 5).dvd_mul.mp h5sig) with h | h
    · rcases ((by norm_num : Nat.Prime 5).dvd_mul.mp h) with h | h
      · rcases ((by norm_num : Nat.Prime 5).dvd_mul.mp h) with h | h
        · exact absurd h h5ne3
        · exact absurd h h5ne5
      · exact absurd h h5ne17
    · exact h
  have h17S : 17 ∣ ∑ i ∈ Finset.range (2*e + 1), q4 ^ i := by
    rw [hsigma] at h17sig
    rcases ((by norm_num : Nat.Prime 17).dvd_mul.mp h17sig) with h | h
    · rcases ((by norm_num : Nat.Prime 17).dvd_mul.mp h) with h | h
      · rcases ((by norm_num : Nat.Prime 17).dvd_mul.mp h) with h | h
        · exact absurd h h17ne3
        · exact absurd h h17ne5
      · exact absurd h h17ne17
    · exact h
  -- transfer to ZMod power relations and apply the order argument
  clear hfac hsigma hrel h3sig h5sig h17m h17sig
  clear h3ne3 h3ne5 h3ne17 h5ne3 h5ne5 h5ne17 h17ne3 h17ne5 h17ne17
  have hgeom := geom_mul_sub_one q4 (2*e + 1) hq4pos
  have h3ndvdq4' : ¬ 3 ∣ q4 := h3ndvdq4
  have h5ndvdq4 : ¬ 5 ∣ q4 := by
    intro hd
    have h := hq4.eq_one_or_self_of_dvd 5 hd
    rcases h with h | h <;> omega
  have h17ndvdq4 : ¬ 17 ∣ q4 := by
    intro hd
    have h := hq4.eq_one_or_self_of_dvd 17 hd
    rcases h with h | h <;> omega
  have hodd : Odd (2*e + 1) := ⟨e, by ring⟩
  have h2cop : Nat.Coprime 2 (2*e + 1) := Nat.coprime_two_left.mpr hodd
  have hpw1 : 1 ≤ q4 ^ (2*e + 1) := Nat.one_le_pow _ _ hq4pos
  -- r = 3
  have hmod3 : (q4 : ZMod 3) ^ (2*e + 1) = 1 := by
    have h3dvd : 3 ∣ q4 ^ (2*e + 1) - 1 := by
      rw [← hgeom]
      exact dvd_mul_of_dvd_left h3S _
    have hzero : ((q4 ^ (2*e + 1) - 1 : Nat) : ZMod 3) = 0 :=
      (ZMod.natCast_eq_zero_iff (q4 ^ (2*e + 1) - 1) 3).mpr h3dvd
    have hcast : ((q4 ^ (2*e + 1) - 1 : Nat) : ZMod 3) =
        (q4 : ZMod 3) ^ (2*e + 1) - 1 := by
      rw [Nat.cast_sub hpw1, Nat.cast_pow, Nat.cast_one]
    rw [hcast] at hzero
    exact sub_eq_zero.mp hzero
  have hdvdq3 : 3 ∣ q4 - 1 := by
    have hne : (q4 : ZMod 3) ≠ 0 :=
      fun h0 => h3ndvdq4' ((ZMod.natCast_eq_zero_iff q4 3).mp h0)
    have hdvd : orderOf ((q4 : ℕ) : ZMod 3) ∣ 2 := by
      haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      have hf : ((q4 : ℕ) : ZMod 3) ^ (3 - 1) = 1 := ZMod.pow_card_sub_one_eq_one hne
      simpa using (orderOf_dvd_iff_pow_eq_one.mpr hf)
    have hodd' : orderOf ((q4 : ℕ) : ZMod 3) ∣ 2*e + 1 :=
      orderOf_dvd_iff_pow_eq_one.mpr hmod3
    have hone : orderOf ((q4 : ℕ) : ZMod 3) = 1 := by
      have hcop : Nat.Coprime (2 : ℕ) (2*e + 1) := h2cop
      exact Nat.eq_one_of_dvd_coprimes hcop hdvd hodd'
    have h1 : ((q4 : ℕ) : ZMod 3) = 1 := orderOf_eq_one_iff.mp hone
    have h2 : ((q4 - 1 : Nat) : ZMod 3) = 0 := by
      rw [Nat.cast_sub hq4pos, h1]
      simp
    exact (ZMod.natCast_eq_zero_iff (q4 - 1) 3).mp h2
  -- r = 5
  have hmod5 : (q4 : ZMod 5) ^ (2*e + 1) = 1 := by
    have h5dvd : 5 ∣ q4 ^ (2*e + 1) - 1 := by
      rw [← hgeom]
      exact dvd_mul_of_dvd_left h5S _
    have hzero : ((q4 ^ (2*e + 1) - 1 : Nat) : ZMod 5) = 0 :=
      (ZMod.natCast_eq_zero_iff (q4 ^ (2*e + 1) - 1) 5).mpr h5dvd
    have hcast : ((q4 ^ (2*e + 1) - 1 : Nat) : ZMod 5) =
        (q4 : ZMod 5) ^ (2*e + 1) - 1 := by
      rw [Nat.cast_sub hpw1, Nat.cast_pow, Nat.cast_one]
    rw [hcast] at hzero
    exact sub_eq_zero.mp hzero
  have hdvdq5 : 5 ∣ q4 - 1 := by
    have hne : (q4 : ZMod 5) ≠ 0 :=
      fun h0 => h5ndvdq4 ((ZMod.natCast_eq_zero_iff q4 5).mp h0)
    have hdvd : orderOf ((q4 : ℕ) : ZMod 5) ∣ 4 := by
      haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      have hf : ((q4 : ℕ) : ZMod 5) ^ (5 - 1) = 1 := ZMod.pow_card_sub_one_eq_one hne
      simpa using (orderOf_dvd_iff_pow_eq_one.mpr hf)
    have hodd' : orderOf ((q4 : ℕ) : ZMod 5) ∣ 2*e + 1 :=
      orderOf_dvd_iff_pow_eq_one.mpr hmod5
    have hone : orderOf ((q4 : ℕ) : ZMod 5) = 1 := by
      have hcop : Nat.Coprime (4 : ℕ) (2*e + 1) := by
        have h := (Nat.coprime_pow_left_iff (n := 2) (by norm_num) 2 (2*e + 1)).mpr h2cop
        simpa using h
      exact Nat.eq_one_of_dvd_coprimes hcop hdvd hodd'
    have h1 : ((q4 : ℕ) : ZMod 5) = 1 := orderOf_eq_one_iff.mp hone
    have h2 : ((q4 - 1 : Nat) : ZMod 5) = 0 := by
      rw [Nat.cast_sub hq4pos, h1]
      simp
    exact (ZMod.natCast_eq_zero_iff (q4 - 1) 5).mp h2
  -- r = 17
  have hmod17 : (q4 : ZMod 17) ^ (2*e + 1) = 1 := by
    have h17dvd : 17 ∣ q4 ^ (2*e + 1) - 1 := by
      rw [← hgeom]
      exact dvd_mul_of_dvd_left h17S _
    have hzero : ((q4 ^ (2*e + 1) - 1 : Nat) : ZMod 17) = 0 :=
      (ZMod.natCast_eq_zero_iff (q4 ^ (2*e + 1) - 1) 17).mpr h17dvd
    have hcast : ((q4 ^ (2*e + 1) - 1 : Nat) : ZMod 17) =
        (q4 : ZMod 17) ^ (2*e + 1) - 1 := by
      rw [Nat.cast_sub hpw1, Nat.cast_pow, Nat.cast_one]
    rw [hcast] at hzero
    exact sub_eq_zero.mp hzero
  have hdvdq17 : 17 ∣ q4 - 1 := by
    have hne : (q4 : ZMod 17) ≠ 0 :=
      fun h0 => h17ndvdq4 ((ZMod.natCast_eq_zero_iff q4 17).mp h0)
    have hdvd : orderOf ((q4 : ℕ) : ZMod 17) ∣ 16 := by
      haveI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
      have hf : ((q4 : ℕ) : ZMod 17) ^ (17 - 1) = 1 := ZMod.pow_card_sub_one_eq_one hne
      simpa using (orderOf_dvd_iff_pow_eq_one.mpr hf)
    have hodd' : orderOf ((q4 : ℕ) : ZMod 17) ∣ 2*e + 1 :=
      orderOf_dvd_iff_pow_eq_one.mpr hmod17
    have hone : orderOf ((q4 : ℕ) : ZMod 17) = 1 := by
      have hcop : Nat.Coprime (16 : ℕ) (2*e + 1) := by
        have h := (Nat.coprime_pow_left_iff (n := 4) (by norm_num) 2 (2*e + 1)).mpr h2cop
        simpa using h
      exact Nat.eq_one_of_dvd_coprimes hcop hdvd hodd'
    have h1 : ((q4 : ℕ) : ZMod 17) = 1 := orderOf_eq_one_iff.mp hone
    have h2 : ((q4 - 1 : Nat) : ZMod 17) = 0 := by
      rw [Nat.cast_sub hq4pos, h1]
      simp
    exact (ZMod.natCast_eq_zero_iff (q4 - 1) 17).mp h2
  -- 255 divides q4 - 1
  have hdvd255 : 255 ∣ q4 - 1 := by
    have h15 : 15 ∣ q4 - 1 :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 5) hdvdq3 hdvdq5
    have h := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 15 17) h15 hdvdq17
    simpa using h
  exact hdvd255

set_option maxHeartbeats 1200000 in
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
    (hD : D = 135) :
    q4 = 1021 ∨ q4 = 1531 ∨ q4 = 2551 ∨ q4 = 3061 ∨ q4 = 3571 ∨ q4 = 4591 := by
  subst hD
  have hp269 : p = 269 := by omega
  subst hp269
  have hq4pos : 1 ≤ q4 := by omega
  have hdvd255 : 255 ∣ q4 - 1 :=
    opn_d135_congruence m a b c e q4 sigma hfac hsigma hrel hq4 hq4gt ha hb hc he
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
  have r3 : (3 : ℕ) ^ (2*a + 1) = 3 ^ (2*a) * 3 := pow_succ 3 (2*a)
  have r5 : (5 : ℕ) ^ (2*b + 1) = 5 ^ (2*b) * 5 := pow_succ 5 (2*b)
  have r17 : (17 : ℕ) ^ (2*c + 1) = 17 ^ (2*c) * 17 := pow_succ 17 (2*c)
  have rq : q4 ^ (2*e + 1) = q4 ^ (2*e) * q4 := pow_succ q4 (2*e)
  have p3b := p3
  rw [r3, r5, r17, rq] at p3b
  have fin : 128 * (q4 - 1) * 135 * sigma < 135 * 255 * q4 * m ^ 2 := by
    rw [hsigma, hfac]
    linear_combination 135 * p3b
  have hm2 : 0 < m ^ 2 := by rw [hfac]; positivity
  have fin2 : (128 * (q4 - 1) * 269) * m ^ 2 < (135 * 255 * q4) * m ^ 2 := by
    have hrw : 128 * (q4 - 1) * 135 * sigma = (128 * (q4 - 1) * 269) * m ^ 2 := by
      linear_combination 128 * (q4 - 1) * hrel
    rw [← hrw]
    exact fin
  have fin3 : 128 * (q4 - 1) * 269 < 135 * 255 * q4 :=
    lt_of_mul_lt_mul_right fin2 (le_of_lt hm2)
  have hbound : q4 ≤ 4918 := by omega
  -- finite enumeration of the congruent primes
  obtain ⟨k, hk⟩ := hdvd255
  have hkq : q4 = 255 * k + 1 := by omega
  have hk19 : k ≤ 19 := by omega
  interval_cases k <;> (rw [hkq] at hq4 ⊢) <;> first
    | decide
    | (exfalso; norm_num at hq4)
