-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_half_exp17_ne_one_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-20T01:59:54.843992+00:00
-- url     : https://prove2.me/submissions/2eced181-e5fa-4bbf-895a-ebca6f1ac908

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_seventeen_ge_two
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_even_order
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_half_exp3_ge_four_or_cases_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_half_exp5_ge_four_or_cases_v1

open OddPerfectNumber

-- The two window bounds are pure linear arithmetic in `D` once `p = 2D - 1` is
-- substituted.  Isolating them keeps `omega` away from the ambient `∑`/product
-- context, which is what defeated the in-line versions.

theorem opn_q17_window_ge (D p : Nat) (hp1 : p + 1 = 2 * D)
    (h : 9841 * 3906 * 307 * 308 * D ≤ 6561 * 3125 * 289 * 307 * p) : 511 ≤ D := by
  have e1 : (9841 * 3906 * 307 * 308 : Nat) = 2763 * 1315466152 := by norm_num
  have e2 : (6561 * 3125 * 289 * 307 : Nat) = 2763 * 658378125 := by norm_num
  rw [e1, e2] at h
  have h2 : 1315466152 * D ≤ 658378125 * p := by
    have hmul : 2763 * (1315466152 * D) ≤ 2763 * (658378125 * p) := by
      calc 2763 * (1315466152 * D) = 2763 * 1315466152 * D := by ring
        _ ≤ 2763 * 658378125 * p := h
        _ = 2763 * (658378125 * p) := by ring
    exact Nat.le_of_mul_le_mul_left hmul (by norm_num)
  omega

theorem opn_q17_window_le (D p : Nat) (hp2 : p = 2 * D - 1)
    (h : 128 * (307 - 1) * p < 255 * 307 * D) : D ≤ 767 := by
  omega

-- `OddPerfectNumber.k_one_q2_five_q3_seventeen_half_exp17_ne_one_v1`
--
-- In the canonical q2=5, q3=17 coordinates the 17-half-exponent cannot be 1.
--
-- `c = 1` gives `sigma(17^2) = 307` as a factor of `sigma = p * d`, so `307`
-- is `p` (which forces the even `D = 154` against `Odd m`) or divides `d`, and
-- then `307 | m` puts `307` in the support, leaving `q4 = 307`.  That step is
-- proved inline below rather than imported, to keep the dependency graph small.
--
-- With `q4 = 307` and `4 <= a`, `4 <= b`, `1 <= e` the Euler relation
-- `D * sigma = p * m^2` (`D := (p+1)/2`) squeezes `D` into the window
-- `511 <= D <= 767`:
--
--   lower: `9841 * 3906 * 307 * 308 * m^2 <= 6561 * 3125 * 289 * 307 * sigma`
--          (`9841/6561` from `geom_ratio_lower_three_ge_eight`,
--           `3906/3125` from `geom_ratio_lower_five_ge_six`,
--           `307/289` from `geom_ratio_lower_seventeen_ge_two`, and the top two
--           terms `309/307 >= 308/307` of the `q4` component),
--   upper: `128 * 306 * sigma < 255 * 307 * m^2` (the strict four-factor product
--          `2*S_3 < 3^(2a+1)`, `4*S_5 < 5^(2b+1)`, `16*S_17 < 17^(2c+1)`,
--           `306*S_307 < 307^(2e+1)`).
--
-- `D | m^2` and the support `{3,5,17,307}` then force
-- `D = 3^i 5^j 17^k 307^l`; size gives `i <= 6`, `j <= 4`, `k <= 2`,
-- `l <= 1`, and a finite check leaves `D in {625, 675, 729, 765}`.  Only
-- `D = 625` makes `p = 2D - 1 = 1249` prime.
--
-- Finally `D = 625 = 5^4 < 5^(2b)` forces `5 | sigma`; `5` divides none of
-- `S_3(2a)`, `S_5(2b)`, `307`, so `5 | S_307(2e)`, against
-- `geom_sum_not_dvd_of_even_order` (`orderOf (307 : ZMod 5) = 4`).

set_option maxHeartbeats 4000000 in
theorem solution (p m d q4 a b c e sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 17 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 17 < q4)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 17 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 17 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 2*a)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2*b)
    (h17mem : 17 ∈ (m ^ 2).primeFactors)
    (h17exp : (m ^ 2).factorization 17 = 2*c)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e) :
    c ≠ 1 := by
  intro hc1
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0] at hm
    simp at hm
  have hq4v : q4 = 307 := by
    have hsigpd : sigma = p * d := by rw [hglobal, hsig]
    have hS17 : (∑ i ∈ Finset.range (2*c + 1), 17 ^ i) = 307 := by
      rw [hc1]
      norm_num
    have h307sig : 307 ∣ sigma := by
      rw [hsigma, hS17]
      exact ⟨(∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
        (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
        (∑ i ∈ Finset.range (2*e + 1), q4 ^ i), by ring⟩
    rw [hsigpd] at h307sig
    rcases (by norm_num : Nat.Prime 307).dvd_mul.mp h307sig with h | h
    · have hp307 : p = 307 := by
        rcases hp.eq_one_or_self_of_dvd 307 h with h' | h'
        · exact absurd h' (by norm_num : ¬ (307 : Nat) = 1)
        · exact h'.symm
      exfalso
      have h2m : (2 : Nat) ∣ m ^ 2 := by
        rw [hprod, hp307]
        norm_num
        exact dvd_mul_of_dvd_left (by norm_num : (2 : Nat) ∣ 154) d
      have h2md : (2 : Nat) ∣ m := (by norm_num : Nat.Prime 2).dvd_of_dvd_pow h2m
      exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h2md)
    · have hmd : 307 ∣ m := by
        have hmd2 : 307 ∣ m ^ 2 := dvd_trans h ⟨(p + 1) / 2, by rw [hprod]; ring⟩
        exact (by norm_num : Nat.Prime 307).dvd_of_dvd_pow hmd2
      have hmem : 307 ∈ m.primeFactors :=
        (Nat.mem_primeFactors).2 ⟨by norm_num, hmd, hm0⟩
      rcases hsupport 307 hmem with h' | h' | h' | h'
      · omega
      · omega
      · omega
      · exact h'.symm
  have ha4 : 4 ≤ a := by
    rcases k_one_q2_five_q3_seventeen_half_exp3_ge_four_or_cases_v1 p m d q4 a b c e sigma
      hp hp4 hm hpm hprod hsig hsupport hq4prime hq4gt hfac hsigma hglobal
      h3mem h3exp h5mem h5exp h17mem h17exp ha hb hc he with h | h | h
    · exact h
    · omega
    · omega
  have hb4 : 4 ≤ b := by
    rcases k_one_q2_five_q3_seventeen_half_exp5_ge_four_or_cases_v1 p m d q4 a b c e sigma
      hp hp4 hm hpm hprod hsig hsupport hq4prime hq4gt hfac hsigma hglobal
      h3mem h3exp h5mem h5exp h17mem h17exp ha hb hc he with h | h | h
    · exact h
    · omega
    · omega
  obtain ⟨D, hDdef⟩ : ∃ D : Nat, D = (p + 1) / 2 := ⟨_, rfl⟩
  have hprodD : m ^ 2 = D * d := by rw [hDdef]; exact hprod
  have hp2 : p = 2 * D - 1 := by omega
  have hp1 : p + 1 = 2 * D := by omega
  have hm2pos : 0 < m ^ 2 := by rw [hfac]; positivity
  have hDpos : 0 < D := by omega
  have hDdvd : D ∣ m ^ 2 := ⟨d, hprodD⟩
  have hrel : D * sigma = p * m ^ 2 := by
    have h1 : sigma = p * d := by rw [hglobal, hsig]
    rw [h1, hprodD]
    ring
  -- ---------------------------------------------------------------- window lower
  have e3 : 9841 * 3 ^ (2*a) ≤ 6561 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) :=
    geom_ratio_lower_three_ge_eight (2*a) (by omega)
  have e5 : 3906 * 5 ^ (2*b) ≤ 3125 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) :=
    geom_ratio_lower_five_ge_six (2*b) (by omega)
  have e17 : 307 * 17 ^ (2*c) ≤ 289 * (∑ i ∈ Finset.range (2*c + 1), 17 ^ i) :=
    geom_ratio_lower_seventeen_ge_two (2*c) (by omega)
  have hsplit307 : (∑ i ∈ Finset.range (2*e + 1), 307 ^ i) =
      (∑ i ∈ Finset.range (2*e), 307 ^ i) + 307 ^ (2*e) := by
    rw [Finset.sum_range_succ]
  have hlow307 : 307 ^ (2*e - 1) ≤ ∑ i ∈ Finset.range (2*e), 307 ^ i :=
    Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
  have hpow307 : 307 * 307 ^ (2*e - 1) = 307 ^ (2*e) := by
    rw [← pow_succ']
    congr 1
    omega
  have eqq : 308 * 307 ^ (2*e) ≤ 307 * (∑ i ∈ Finset.range (2*e + 1), 307 ^ i) := by
    rw [hsplit307]
    nlinarith [hlow307, hpow307]
  have hlo : 9841 * 3906 * 307 * 308 * m ^ 2 ≤ 6561 * 3125 * 289 * 307 * sigma := by
    have s1 : (9841 * 3 ^ (2*a)) * (3906 * 5 ^ (2*b)) ≤
        (6561 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i)) *
          (3125 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i)) :=
      Nat.mul_le_mul e3 e5
    have s2 : ((9841 * 3 ^ (2*a)) * (3906 * 5 ^ (2*b))) * (307 * 17 ^ (2*c)) ≤
        ((6561 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i)) *
          (3125 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i))) *
        (289 * (∑ i ∈ Finset.range (2*c + 1), 17 ^ i)) :=
      Nat.mul_le_mul s1 e17
    have s3 : (((9841 * 3 ^ (2*a)) * (3906 * 5 ^ (2*b))) * (307 * 17 ^ (2*c))) *
        (308 * 307 ^ (2*e)) ≤
        (((6561 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i)) *
          (3125 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i))) *
        (289 * (∑ i ∈ Finset.range (2*c + 1), 17 ^ i))) *
        (307 * (∑ i ∈ Finset.range (2*e + 1), 307 ^ i)) :=
      Nat.mul_le_mul s2 eqq
    rw [hfac, hsigma, hq4v]
    convert s3 using 1 <;> ring
  have hB : 9841 * 3906 * 307 * 308 * D ≤ 6561 * 3125 * 289 * 307 * p := by
    have h1 := Nat.mul_le_mul_right D hlo
    have h2 : (6561 * 3125 * 289 * 307 * sigma) * D =
        6561 * 3125 * 289 * 307 * (p * m ^ 2) := by
      linear_combination 6561 * 3125 * 289 * 307 * hrel
    rw [h2] at h1
    have h3 : (9841 * 3906 * 307 * 308 * m ^ 2) * D =
        (9841 * 3906 * 307 * 308 * D) * m ^ 2 := by ring
    rw [h3] at h1
    have h4 : (9841 * 3906 * 307 * 308 * D) * m ^ 2 ≤
        (6561 * 3125 * 289 * 307 * p) * m ^ 2 := by
      nlinarith [h1]
    exact Nat.le_of_mul_le_mul_right h4 hm2pos
  have hDge : 511 ≤ D := opn_q17_window_ge D p hp1 hB
  -- ---------------------------------------------------------------- window upper
  have g3 : 2 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) + 1 = 3 ^ (2*a + 1) := by
    rw [mul_comm 2 _]
    exact geom_sum_mul_add 2 (2*a + 1)
  have g5 : 4 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) + 1 = 5 ^ (2*b + 1) := by
    rw [mul_comm 4 _]
    exact geom_sum_mul_add 4 (2*b + 1)
  have g17 : 16 * (∑ i ∈ Finset.range (2*c + 1), 17 ^ i) + 1 = 17 ^ (2*c + 1) := by
    rw [mul_comm 16 _]
    exact geom_sum_mul_add 16 (2*c + 1)
  have gq : (307 - 1) * (∑ i ∈ Finset.range (2*e + 1), 307 ^ i) + 1 =
      307 ^ (2*e + 1) := by
    have h := geom_sum_mul_add (307 - 1) (2*e + 1)
    rw [Nat.sub_add_cancel (by norm_num : 1 ≤ 307)] at h
    rw [mul_comm (307 - 1) _]
    exact h
  have f1 : 2 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) < 3 ^ (2*a + 1) := by omega
  have f2 : 4 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) < 5 ^ (2*b + 1) := by omega
  have f3 : 16 * (∑ i ∈ Finset.range (2*c + 1), 17 ^ i) < 17 ^ (2*c + 1) := by omega
  have f4 : (307 - 1) * (∑ i ∈ Finset.range (2*e + 1), 307 ^ i) <
      307 ^ (2*e + 1) := by omega
  have l2 : 4 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) ≤ 5 ^ (2*b + 1) := by omega
  have l3 : 16 * (∑ i ∈ Finset.range (2*c + 1), 17 ^ i) ≤ 17 ^ (2*c + 1) := by omega
  have l4 : (307 - 1) * (∑ i ∈ Finset.range (2*e + 1), 307 ^ i) ≤
      307 ^ (2*e + 1) := by omega
  have hBpos : 0 < 5 ^ (2*b + 1) := by positivity
  have hCpos : 0 < 17 ^ (2*c + 1) := by positivity
  have hEpos : 0 < 307 ^ (2*e + 1) := by positivity
  have p1 : (2 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i)) *
      (4 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i)) < 3 ^ (2*a + 1) * 5 ^ (2*b + 1) :=
    Nat.mul_lt_mul_of_lt_of_le f1 l2 hBpos
  have p2 : ((2 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i)) *
      (4 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i))) *
      (16 * (∑ i ∈ Finset.range (2*c + 1), 17 ^ i)) <
      (3 ^ (2*a + 1) * 5 ^ (2*b + 1)) * 17 ^ (2*c + 1) :=
    Nat.mul_lt_mul_of_lt_of_le p1 l3 hCpos
  have p3 : (((2 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i)) *
      (4 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i))) *
      (16 * (∑ i ∈ Finset.range (2*c + 1), 17 ^ i))) *
      ((307 - 1) * (∑ i ∈ Finset.range (2*e + 1), 307 ^ i)) <
      ((3 ^ (2*a + 1) * 5 ^ (2*b + 1)) * 17 ^ (2*c + 1)) * 307 ^ (2*e + 1) :=
    Nat.mul_lt_mul_of_lt_of_le p2 l4 hEpos
  have r3 : (3 : Nat) ^ (2*a + 1) = 3 ^ (2*a) * 3 := pow_succ 3 (2*a)
  have r5 : (5 : Nat) ^ (2*b + 1) = 5 ^ (2*b) * 5 := pow_succ 5 (2*b)
  have r17 : (17 : Nat) ^ (2*c + 1) = 17 ^ (2*c) * 17 := pow_succ 17 (2*c)
  have rq : (307 : Nat) ^ (2*e + 1) = 307 ^ (2*e) * 307 := pow_succ 307 (2*e)
  have p3b := p3
  rw [r3, r5, r17, rq] at p3b
  have hup : 128 * (307 - 1) * sigma < 255 * 307 * m ^ 2 := by
    rw [hsigma, hfac, hq4v]
    linear_combination p3b
  have hA : 128 * (307 - 1) * p < 255 * 307 * D := by
    have h1 := Nat.mul_lt_mul_of_pos_right hup hDpos
    have h2 : (128 * (307 - 1) * sigma) * D = 128 * (307 - 1) * (p * m ^ 2) := by
      linear_combination 128 * (307 - 1) * hrel
    rw [h2] at h1
    have h3 : (255 * 307 * m ^ 2) * D = (255 * 307 * D) * m ^ 2 := by ring
    rw [h3] at h1
    have h4 : (128 * (307 - 1) * p) * m ^ 2 < (255 * 307 * D) * m ^ 2 := by
      nlinarith [h1]
    exact lt_of_mul_lt_mul_right h4 (le_of_lt hm2pos)
  have hDle : D ≤ 767 := by
    exact opn_q17_window_le D p hp2 hA
  -- ------------------------------------------- D in the support, then enumeration
  have hDne : D ≠ 0 := by omega
  have hDp : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 17 ∨ r = 307 := by
    intro r hrp hrd
    have hrd2 : r ∣ m ^ 2 := dvd_trans hrd hDdvd
    have hrdm : r ∣ m := hrp.dvd_of_dvd_pow hrd2
    have hmem : r ∈ m.primeFactors := (Nat.mem_primeFactors).2 ⟨hrp, hrdm, hm0⟩
    rcases hsupport r hmem with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (by omega)))
  let i := D.factorization 3
  let j := D.factorization 5
  let k := D.factorization 17
  let l := D.factorization 307
  have hzero : ∀ r, r ≠ 3 → r ≠ 5 → r ≠ 17 → r ≠ 307 → D.factorization r = 0 := by
    intro r hr3 hr5 hr17 hr307
    by_cases hrp : r.Prime
    · by_cases hrd : r ∣ D
      · rcases hDp r hrp hrd with h | h | h | h
        · exact absurd h hr3
        · exact absurd h hr5
        · exact absurd h hr17
        · exact absurd h hr307
      · exact (Nat.factorization_eq_zero_iff D r).2 (Or.inr (Or.inl hrd))
    · exact (Nat.factorization_eq_zero_iff D r).2 (Or.inl hrp)
  let f : Nat →₀ Nat :=
    Finsupp.single 3 i + Finsupp.single 5 j + Finsupp.single 17 k + Finsupp.single 307 l
  have hfd : f = D.factorization := by
    ext r
    by_cases h3 : r = 3
    · subst r
      simp [f, i, j, k, l]
    · by_cases h5 : r = 5
      · subst r
        simp [f, i, j, k, l]
      · by_cases h17 : r = 17
        · subst r
          simp [f, i, j, k, l]
        · by_cases h307 : r = 307
          · subst r
            simp [f, i, j, k, l]
          · simp only [f, Finsupp.add_apply, Finsupp.single_apply]
            have h3' : 3 ≠ r := by omega
            have h5' : 5 ≠ r := by omega
            have h17' : 17 ≠ r := by omega
            have h307' : 307 ≠ r := by omega
            simp [h3, h5, h17, h307, h3', h5', h17', h307',
              hzero r h3 h5 h17 h307]
  have hform : D = 3^i * 5^j * 17^k * 307^l := by
    have hprod2 : f.prod (fun r n => r ^ n) = D := by
      calc f.prod (fun r n => r ^ n) = D.factorization.prod (fun r n => r ^ n) := by rw [hfd]
        _ = D := Nat.prod_factorization_pow_eq_self hDne
    simpa [f, Finsupp.prod_add_index', Nat.pow_add] using hprod2.symm
  have hDprod : 3 ^ i * 5 ^ j * 17 ^ k * 307 ^ l = D := hform.symm
  have hi : i ≤ 6 := by
    by_contra h
    have h6 : 6 < i := Nat.lt_of_not_le h
    have h7 : 7 ≤ i := h6
    have h3i : 3 ^ i ≤ D :=
      Nat.le_of_dvd hDpos ⟨5 ^ j * 17 ^ k * 307 ^ l, by rw [hform]; ring⟩
    have h7' : 3 ^ 7 ≤ D := le_trans (Nat.pow_le_pow_right (by norm_num) h7) h3i
    have hbig : (2187 : Nat) ≤ D := by norm_num at h7'; exact h7'
    have hcontra : (2187 : Nat) ≤ 767 := le_trans hbig hDle
    norm_num at hcontra
  have hj : j ≤ 4 := by
    by_contra h
    have h4 : 4 < j := Nat.lt_of_not_le h
    have h5j : 5 ≤ j := h4
    have h5le : 5 ^ j ≤ D :=
      Nat.le_of_dvd hDpos ⟨3 ^ i * 17 ^ k * 307 ^ l, by rw [hform]; ring⟩
    have h5' : 5 ^ 5 ≤ D := le_trans (Nat.pow_le_pow_right (by norm_num) h5j) h5le
    have hbig : (3125 : Nat) ≤ D := by norm_num at h5'; exact h5'
    have hcontra : (3125 : Nat) ≤ 767 := le_trans hbig hDle
    norm_num at hcontra
  have hk : k ≤ 2 := by
    by_contra h
    have h2 : 2 < k := Nat.lt_of_not_le h
    have h17k : 3 ≤ k := h2
    have h17le : 17 ^ k ≤ D :=
      Nat.le_of_dvd hDpos ⟨3 ^ i * 5 ^ j * 307 ^ l, by rw [hform]; ring⟩
    have h17' : 17 ^ 3 ≤ D := le_trans (Nat.pow_le_pow_right (by norm_num) h17k) h17le
    have hbig : (4913 : Nat) ≤ D := by norm_num at h17'; exact h17'
    have hcontra : (4913 : Nat) ≤ 767 := le_trans hbig hDle
    norm_num at hcontra
  have hl : l ≤ 1 := by
    by_contra h
    have h1' : 1 < l := Nat.lt_of_not_le h
    have hl2 : 2 ≤ l := h1'
    have hlle : 307 ^ l ≤ D :=
      Nat.le_of_dvd hDpos ⟨3 ^ i * 5 ^ j * 17 ^ k, by rw [hform]; ring⟩
    have hll' : 307 ^ 2 ≤ D := le_trans (Nat.pow_le_pow_right (by norm_num) hl2) hlle
    have hbig : (94249 : Nat) ≤ D := by norm_num at hll'; exact hll'
    have hcontra : (94249 : Nat) ≤ 767 := le_trans hbig hDle
    norm_num at hcontra
  have hkey : ∀ (x : Fin 7) (y : Fin 5) (z : Fin 3) (w : Fin 2),
      511 ≤ 3 ^ (x : Nat) * 5 ^ (y : Nat) * 17 ^ (z : Nat) * 307 ^ (w : Nat) →
      3 ^ (x : Nat) * 5 ^ (y : Nat) * 17 ^ (z : Nat) * 307 ^ (w : Nat) ≤ 767 →
      3 ^ (x : Nat) * 5 ^ (y : Nat) * 17 ^ (z : Nat) * 307 ^ (w : Nat) ∈
        ({(625 : Nat), 675, 729, 765} : Finset Nat) := by
    decide
  have hbound : 3 ^ i * 5 ^ j * 17 ^ k * 307 ^ l ∈
      ({(625 : Nat), 675, 729, 765} : Finset Nat) := by
    have hge : 511 ≤ 3 ^ i * 5 ^ j * 17 ^ k * 307 ^ l := by
      rw [hDprod]; exact hDge
    have hle : 3 ^ i * 5 ^ j * 17 ^ k * 307 ^ l ≤ 767 := by
      rw [hDprod]; exact hDle
    exact hkey ⟨i, by omega⟩ ⟨j, by omega⟩ ⟨k, by omega⟩ ⟨l, by omega⟩ hge hle
  have hD625 : D = 625 := by
    have hmem := hbound
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h
    · rw [← hDprod]; exact h
    · exfalso
      have hD : D = 675 := by rw [hform, h]
      exact absurd hp (by rw [hp2, hD]; norm_num)
    · exfalso
      have hD : D = 729 := by rw [hform, h]
      exact absurd hp (by rw [hp2, hD]; norm_num)
    · exfalso
      have hD : D = 765 := by rw [hform, h]
      exact absurd hp (by rw [hp2, hD]; norm_num)
  -- ------------------------------------------------------- 5 divides sigma, absurd
  have h5sig : 5 ∣ sigma := by
    have h8b : 8 ≤ 2 * b := by
      have h := Nat.mul_le_mul_left 2 hb4
      norm_num at h
      exact h
    have h52b : (5 : Nat) ^ 5 ∣ 5 ^ (2*b) :=
      pow_dvd_pow 5 (le_trans (by norm_num : (5 : Nat) ≤ 8) h8b)
    have h552 : (5 : Nat) ^ 5 ∣ m ^ 2 := by
      have h1 : (5 : Nat) ^ 5 ∣ 3 ^ (2*a) * 5 ^ (2*b) := dvd_mul_of_dvd_right h52b _
      have h2 : (5 : Nat) ^ 5 ∣ (3 ^ (2*a) * 5 ^ (2*b)) * 17 ^ (2*c) :=
        dvd_mul_of_dvd_left h1 _
      have h3 : (5 : Nat) ^ 5 ∣ ((3 ^ (2*a) * 5 ^ (2*b)) * 17 ^ (2*c)) * 307 ^ (2*e) :=
        dvd_mul_of_dvd_left h2 _
      rw [hfac, hq4v]
      exact h3
    have hrel5 : 5 ^ 4 * sigma = p * m ^ 2 := by
      have h := hrel
      rw [hD625] at h
      norm_num at h <;> norm_num
      exact h
    have h55dvd : (5 : Nat) ^ 5 ∣ p * m ^ 2 := dvd_mul_of_dvd_right h552 p
    have h55dvd' : (5 : Nat) ^ 5 ∣ 5 ^ 4 * sigma := by rw [hrel5]; exact h55dvd
    have h55' : (5 : Nat) ^ 4 * 5 ∣ 5 ^ 4 * sigma := by simpa [pow_succ] using h55dvd'
    exact (Nat.mul_dvd_mul_iff_left (by positivity : 0 < (5 : Nat) ^ 4)).mp h55'
  have h5ne3 : ¬ 5 ∣ ∑ i ∈ Finset.range (2*a + 1), 3 ^ i := by
    refine geom_sum_not_dvd_of_even_order (p := 5) (q := 3) (e := a) ?_
    have hnot : ¬ (((3 : Nat) : ZMod 5)) ^ 2 ^ 1 = 1 := by decide
    have hfin : (((3 : Nat) : ZMod 5)) ^ 2 ^ (1 + 1) = 1 := by decide
    have hord : orderOf (((3 : Nat) : ZMod 5)) = 4 := by
      have h := orderOf_eq_prime_pow (p := 2) (n := 1) hnot hfin
      simpa using h
    rw [hord]
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
  have h5not307 : ¬ 5 ∣ ∑ i ∈ Finset.range (2*e + 1), 307 ^ i := by
    refine geom_sum_not_dvd_of_even_order (p := 5) (q := 307) (e := e) ?_
    have h307 : ((307 : Nat) : ZMod 5) = ((2 : Nat) : ZMod 5) := by decide
    rw [h307]
    have hnot : ¬ (((2 : Nat) : ZMod 5)) ^ 2 ^ 1 = 1 := by decide
    have hfin : (((2 : Nat) : ZMod 5)) ^ 2 ^ (1 + 1) = 1 := by decide
    have hord : orderOf (((2 : Nat) : ZMod 5)) = 4 := by
      have h := orderOf_eq_prime_pow (p := 2) (n := 1) hnot hfin
      simpa using h
    rw [hord]
    exact ⟨2, by norm_num⟩
  have h5ne17 : ¬ 5 ∣ ∑ i ∈ Finset.range (2*c + 1), 17 ^ i := by
    refine geom_sum_not_dvd_of_even_order (p := 5) (q := 17) (e := c) ?_
    have h17c : ((17 : Nat) : ZMod 5) = ((2 : Nat) : ZMod 5) := by decide
    rw [h17c]
    have hnot : ¬ (((2 : Nat) : ZMod 5)) ^ 2 ^ 1 = 1 := by decide
    have hfin : (((2 : Nat) : ZMod 5)) ^ 2 ^ (1 + 1) = 1 := by decide
    have hord : orderOf (((2 : Nat) : ZMod 5)) = 4 := by
      have h := orderOf_eq_prime_pow (p := 2) (n := 1) hnot hfin
      simpa using h
    rw [hord]
    exact ⟨2, by norm_num⟩
  have h5p : Nat.Prime 5 := by norm_num
  rw [hsigma, hq4v] at h5sig
  rcases h5p.dvd_mul.mp h5sig with h | h
  · rcases h5p.dvd_mul.mp h with h | h
    · rcases h5p.dvd_mul.mp h with h | h
      · exact absurd h h5ne3
      · exact absurd h h5ne5
    · exact absurd h h5ne17
  · exact absurd h h5not307
