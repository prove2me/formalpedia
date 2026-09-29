-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_D255_q4_candidates_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-19T22:27:30.221975+00:00
-- url     : https://prove2.me/submissions/ffc900b0-5c5f-4a73-99ea-19318c72252b

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_even_order
import Theorems.Thm_OddPerfectNumber_order_three_mod_five_eq_four

open OddPerfectNumber

-- `OddPerfectNumber.k_one_q2_five_q3_seventeen_D255_q4_candidates_v1`
--
-- Half-exponent four-support configuration `m^2 = 3^(2a) * 5^(2b) * 17^(2c) * q4^(2e)`
-- with `D = 255` (so `p = 2 * D - 1 = 509`) and the Euler relation
-- `D * sigma = p * m^2`.
--
-- Here every prime of `D = 3 * 5 * 17` divides `D`, so the `r ∤ D` shortcut of
-- the `D = 289` lemmas does not apply.  Instead cancel `r = 5` resp. `r = 17`
-- between the two sides of `m^2 = 3^(2a) 5^(2b) 17^(2c) q4^(2e)` and `D * sigma`:
-- since `2b >= 2 > v_5(D) = 1` and `2c >= 2 > v_17(D) = 1`, dividing one such
-- factor out of each side produces `5 | sigma` and `17 | sigma`.
--
-- The three non-`q4` local factors are divisible by neither `5` nor `17`
-- (order arguments for `S_3`, `S_5`; an explicit tail argument for the self
-- factor `S_17`), so `5 | S_q4(2e)` and `17 | S_q4(2e)`.  With `q4` a nonzero
-- unit in `ZMod 5` resp. `ZMod 17` and `2e+1` odd, the multiplicative order of
-- `q4` divides `gcd (2e+1) 4 = 1` resp. `gcd (2e+1) 16 = 1`, so
-- `q4 % 5 = 1` and `q4 % 17 = 1`, i.e. `85 | q4 - 1`.
--
-- The abundance bound `128 * (q4 - 1) * 509 < 255 * 255 * q4` (same four-factor
-- product argument as `..._D289_q4_lt_500_v1`) gives `q4 <= 513`.  Hence
-- `q4 = 85 * k + 1` with `k <= 6`, and the only case compatible with `q4` prime
-- (`k = 6`) is `q4 = 511`.

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
    (hD : D = 255) :
    q4 = 511 := by
  subst hD
  have hp509 : p = 509 := by omega
  subst hp509
  have hq4pos : 1 ≤ q4 := by omega
  -- cancel 5: m^2 = 5^2 * K5
  have hm2_5 : m ^ 2 = 25 * (3 ^ (2*a) * 5 ^ (2*b - 2) * 17 ^ (2*c) * q4 ^ (2*e)) := by
    rw [hfac]
    have h5 : (5 : ℕ) ^ (2*b) = 5 ^ 2 * 5 ^ (2*b - 2) := by
      rw [← pow_add]
      congr 1
      omega
    rw [h5]
    ring
  -- cancel 17: m^2 = 17^2 * K17
  have hm2_17 : m ^ 2 = 17 ^ 2 * (3 ^ (2*a) * 5 ^ (2*b) * 17 ^ (2*c - 2) * q4 ^ (2*e)) := by
    rw [hfac]
    have h17 : (17 : ℕ) ^ (2*c) = 17 ^ 2 * 17 ^ (2*c - 2) := by
      rw [← pow_add]
      congr 1
      omega
    rw [h17]
    ring
  -- 5 divides sigma
  have h5sig : 5 ∣ sigma := by
    have h5rel : 51 * sigma = 509 * (5 * (3 ^ (2*a) * 5 ^ (2*b - 2) * 17 ^ (2*c) * q4 ^ (2*e))) := by
      have h := hrel
      rw [hm2_5] at h
      have h' : 5 * (51 * sigma) =
          5 * (509 * (5 * (3 ^ (2*a) * 5 ^ (2*b - 2) * 17 ^ (2*c) * q4 ^ (2*e)))) := by
        nlinarith [h]
      exact Nat.mul_left_cancel (by norm_num) h'
    have hdvd : 5 ∣ 51 * sigma := by
      rw [h5rel]
      exact dvd_mul_of_dvd_right (dvd_mul_right 5 _) 509
    rcases ((by norm_num : Nat.Prime 5).dvd_mul.mp hdvd) with h | h
    · norm_num at h
    · exact h
  -- 17 divides sigma
  have h17sig : 17 ∣ sigma := by
    have h17rel : 15 * sigma = 509 * (17 * (3 ^ (2*a) * 5 ^ (2*b) * 17 ^ (2*c - 2) * q4 ^ (2*e))) := by
      have h := hrel
      rw [hm2_17] at h
      have h' : 17 * (15 * sigma) =
          17 * (509 * (17 * (3 ^ (2*a) * 5 ^ (2*b) * 17 ^ (2*c - 2) * q4 ^ (2*e)))) := by
        nlinarith [h]
      exact Nat.mul_left_cancel (by norm_num) h'
    have hdvd : 17 ∣ 15 * sigma := by
      rw [h17rel]
      exact dvd_mul_of_dvd_right (dvd_mul_right 17 _) 509
    rcases ((by norm_num : Nat.Prime 17).dvd_mul.mp hdvd) with h | h
    · norm_num at h
    · exact h
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
  -- hence the q4 local factor is divisible by 5 and by 17
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
  -- transfer to ZMod power relations
  have hgeom := geom_mul_sub_one q4 (2*e + 1) hq4pos
  have hmod5 : (q4 : ZMod 5) ^ (2*e + 1) = 1 := by
    have h5dvd : 5 ∣ q4 ^ (2*e + 1) - 1 := by
      rw [← hgeom]
      exact dvd_mul_of_dvd_left h5S _
    have hpow1 : 1 ≤ q4 ^ (2*e + 1) := Nat.one_le_pow _ _ hq4pos
    have hzero : ((q4 ^ (2*e + 1) - 1 : Nat) : ZMod 5) = 0 :=
      (ZMod.natCast_eq_zero_iff (q4 ^ (2*e + 1) - 1) 5).mpr h5dvd
    have hcast : ((q4 ^ (2*e + 1) - 1 : Nat) : ZMod 5) =
        (q4 : ZMod 5) ^ (2*e + 1) - 1 := by
      rw [Nat.cast_sub hpow1, Nat.cast_pow, Nat.cast_one]
    rw [hcast] at hzero
    exact sub_eq_zero.mp hzero
  have hmod17 : (q4 : ZMod 17) ^ (2*e + 1) = 1 := by
    have h17dvd : 17 ∣ q4 ^ (2*e + 1) - 1 := by
      rw [← hgeom]
      exact dvd_mul_of_dvd_left h17S _
    have hpow1 : 1 ≤ q4 ^ (2*e + 1) := Nat.one_le_pow _ _ hq4pos
    have hzero : ((q4 ^ (2*e + 1) - 1 : Nat) : ZMod 17) = 0 :=
      (ZMod.natCast_eq_zero_iff (q4 ^ (2*e + 1) - 1) 17).mpr h17dvd
    have hcast : ((q4 ^ (2*e + 1) - 1 : Nat) : ZMod 17) =
        (q4 : ZMod 17) ^ (2*e + 1) - 1 := by
      rw [Nat.cast_sub hpow1, Nat.cast_pow, Nat.cast_one]
    rw [hcast] at hzero
    exact sub_eq_zero.mp hzero
  -- order arguments give q4 % 5 = 1 and q4 % 17 = 1
  have h5ndvdq4 : ¬ 5 ∣ q4 := by
    intro hd
    have h := hq4.eq_one_or_self_of_dvd 5 hd
    rcases h with h | h <;> omega
  have h17ndvdq4 : ¬ 17 ∣ q4 := by
    intro hd
    have h := hq4.eq_one_or_self_of_dvd 17 hd
    rcases h with h | h <;> omega
  have hq4ne5 : (q4 : ZMod 5) ≠ 0 :=
    fun h0 => h5ndvdq4 ((ZMod.natCast_eq_zero_iff q4 5).mp h0)
  have hq4ne17 : (q4 : ZMod 17) ≠ 0 :=
    fun h0 => h17ndvdq4 ((ZMod.natCast_eq_zero_iff q4 17).mp h0)
  have hodd : Odd (2*e + 1) := ⟨e, by ring⟩
  have hdvdodd5 : orderOf ((q4 : ℕ) : ZMod 5) ∣ 2*e + 1 :=
    orderOf_dvd_iff_pow_eq_one.mpr hmod5
  have hdvd5 : orderOf ((q4 : ℕ) : ZMod 5) ∣ 4 := by
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hf : ((q4 : ℕ) : ZMod 5) ^ (5 - 1) = 1 :=
      ZMod.pow_card_sub_one_eq_one hq4ne5
    simpa using (orderOf_dvd_iff_pow_eq_one.mpr hf)
  have hone5 : orderOf ((q4 : ℕ) : ZMod 5) = 1 := by
    have h2 : Nat.Coprime 2 (2*e + 1) := Nat.coprime_two_left.mpr hodd
    have hcop : Nat.Coprime (4 : ℕ) (2*e + 1) := by
      have h := (Nat.coprime_pow_left_iff (n := 2) (by norm_num) 2 (2*e + 1)).mpr h2
      simpa using h
    exact Nat.eq_one_of_dvd_coprimes hcop hdvd5 hdvdodd5
  have hdvdodd17 : orderOf ((q4 : ℕ) : ZMod 17) ∣ 2*e + 1 :=
    orderOf_dvd_iff_pow_eq_one.mpr hmod17
  have hdvd17o : orderOf ((q4 : ℕ) : ZMod 17) ∣ 16 := by
    haveI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
    have hf : ((q4 : ℕ) : ZMod 17) ^ (17 - 1) = 1 :=
      ZMod.pow_card_sub_one_eq_one hq4ne17
    simpa using (orderOf_dvd_iff_pow_eq_one.mpr hf)
  have hone17 : orderOf ((q4 : ℕ) : ZMod 17) = 1 := by
    have h2 : Nat.Coprime 2 (2*e + 1) := Nat.coprime_two_left.mpr hodd
    have hcop : Nat.Coprime (16 : ℕ) (2*e + 1) := by
      have h := (Nat.coprime_pow_left_iff (n := 4) (by norm_num) 2 (2*e + 1)).mpr h2
      simpa using h
    exact Nat.eq_one_of_dvd_coprimes hcop hdvd17o hdvdodd17
  have hdvdq5 : 5 ∣ q4 - 1 := by
    have h1 : ((q4 : ℕ) : ZMod 5) = 1 := orderOf_eq_one_iff.mp hone5
    have h2 : ((q4 - 1 : Nat) : ZMod 5) = 0 := by
      rw [Nat.cast_sub hq4pos, h1]
      simp
    exact (ZMod.natCast_eq_zero_iff (q4 - 1) 5).mp h2
  have hdvdq17 : 17 ∣ q4 - 1 := by
    have h1 : ((q4 : ℕ) : ZMod 17) = 1 := orderOf_eq_one_iff.mp hone17
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
  have fin : 128 * (q4 - 1) * 255 * sigma < 255 * 255 * q4 * m ^ 2 := by
    rw [hsigma, hfac]
    linear_combination 255 * p3b
  have hm2 : 0 < m ^ 2 := by rw [hfac]; positivity
  have fin2 : (128 * (q4 - 1) * 509) * m ^ 2 < (255 * 255 * q4) * m ^ 2 := by
    have hrw : 128 * (q4 - 1) * 255 * sigma = (128 * (q4 - 1) * 509) * m ^ 2 := by
      linear_combination 128 * (q4 - 1) * hrel
    rw [← hrw]
    exact fin
  have fin3 : 128 * (q4 - 1) * 509 < 255 * 255 * q4 :=
    lt_of_mul_lt_mul_right fin2 (le_of_lt hm2)
  have hbound : q4 ≤ 513 := by omega
  -- 85 | q4 - 1
  have hdvd85 : 85 ∣ q4 - 1 :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 5 17) hdvdq5 hdvdq17
  obtain ⟨k, hk⟩ := hdvd85
  have hkq : q4 = 85 * k + 1 := by omega
  have hk6 : k ≤ 6 := by omega
  interval_cases k <;> (rw [hkq] at hq4 ⊢) <;> first
    | decide
    | (exfalso; norm_num at hq4)
