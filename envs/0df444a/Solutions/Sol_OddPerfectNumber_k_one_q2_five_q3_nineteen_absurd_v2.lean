-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_absurd_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T01:26:39.994078+00:00
-- url     : https://prove2.me/submissions/653c38c8-1828-4d1f-bc33-1b2e6415dcce

import Mathlib

set_option autoImplicit false

namespace OPN4afa

open Finset

lemma geom_succ (x n : ℕ) : ∑ i ∈ range (n+1), x^i = x * ∑ i ∈ range n, x^i + 1 := by
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp [pow_succ, mul_comm]

lemma geom_ne (x n : ℕ) : ∑ i ∈ range (2*n+1), x^i ≠ 0 := by
  rw [geom_succ]; omega

lemma geom_nat (x n : ℕ) (hx : 1 ≤ x) :
    (∑ i ∈ range n, x ^ i) * (x - 1) = x ^ n - 1 := by
  have h := geom_sum_mul (x : ℤ) n
  have h1 : 1 ≤ x ^ n := Nat.one_le_pow _ _ hx
  have : (((∑ i ∈ range n, x ^ i) * (x - 1) : ℕ) : ℤ) = ((x ^ n - 1 : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub hx, Nat.cast_sub h1]
    exact h
  exact_mod_cast this

lemma not_self_dvd (x n : ℕ) (hx : 1 < x) : ¬ x ∣ ∑ i ∈ range (n+1), x^i := by
  rw [geom_succ]
  intro h
  have h2 := (Nat.dvd_add_right (dvd_mul_right x _)).mp h
  have := Nat.le_of_dvd one_pos h2
  omega

lemma pow_mod_period (x q k n : ℕ) (hq : 1 < q) (h : x ^ k % q = 1) :
    x ^ n % q = x ^ (n % k) % q := by
  conv_lhs => rw [← Nat.div_add_mod n k, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod, h, one_pow, Nat.one_mod_eq_one.mpr (by omega), one_mul,
    Nat.mod_mod]

lemma mod_one_of_dvd (q N : ℕ) (hq : 1 < q) (hN : 1 ≤ N) (h : q ∣ N - 1) : N % q = 1 := by
  have := (Nat.modEq_iff_dvd' hN).mpr h
  unfold Nat.ModEq at this
  rw [← this]; exact Nat.mod_eq_of_lt hq

lemma dvd_of_mod_one (q N : ℕ) (h : N % q = 1) : q ∣ N - 1 := by
  have := Nat.dvd_sub_mod (n := q) N
  rwa [h] at this

lemma not_dvd_geom (q x k n : ℕ) (hq : 1 < q) (hx : 1 ≤ x) (hkpos : 0 < k) (hk : x ^ k % q = 1)
    (hkeven : 2 ∣ k) (hper : ∀ r < k, r % 2 = 1 → x ^ r % q ≠ 1) (hn : n % 2 = 1) :
    ¬ q ∣ ∑ i ∈ range n, x ^ i := by
  intro hd
  have h1 : q ∣ x ^ n - 1 := by rw [← geom_nat x n hx]; exact Dvd.dvd.mul_right hd _
  have h2 := mod_one_of_dvd q _ hq (Nat.one_le_pow _ _ hx) h1
  rw [pow_mod_period x q k n hq hk] at h2
  exact hper (n % k) (Nat.mod_lt _ hkpos) (by rw [Nat.mod_mod_of_dvd _ hkeven]; exact hn) h2

lemma vbound (q x k n c : ℕ) [hqp : Fact q.Prime] (hqodd : Odd q) (hx1 : 1 < x) (hkpos : 0 < k)
    (hxk : x ^ k % q = 1) (hc : padicValNat q (x ^ k - 1) = c)
    (hper : ∀ r < k, 0 < r → x ^ r % q ≠ 1) :
    padicValNat q (x ^ n - 1) ≤ c + padicValNat q n := by
  have hq1 : 1 < q := hqp.out.one_lt
  by_cases hr : n % k = 0
  · obtain ⟨t, rfl⟩ : k ∣ n := Nat.dvd_of_mod_eq_zero hr
    rcases Nat.eq_zero_or_pos t with ht | ht
    · subst ht; simp
    · have hxq : ¬ q ∣ x ^ k := by
        intro h
        have := Nat.mod_eq_zero_of_dvd h
        omega
      have hlt : 1 < x ^ k := Nat.one_lt_pow (by omega) hx1
      have key := padicValNat.pow_sub_pow (p := q) hqodd (x := x ^ k) (y := 1) hlt
        (by simpa using dvd_of_mod_one q _ hxk) hxq (n := t) (by omega)
      rw [one_pow, ← pow_mul] at key
      rw [key, hc, padicValNat.mul (by omega) (by omega)]
      omega
  · have : ¬ q ∣ x ^ n - 1 := by
      intro h
      have h2 := mod_one_of_dvd q _ hq1 (Nat.one_le_pow _ _ (by omega)) h
      rw [pow_mod_period x q k n hq1 hxk] at h2
      exact hper _ (Nat.mod_lt _ hkpos) (Nat.pos_of_ne_zero hr) h2
    rw [padicValNat.eq_zero_of_not_dvd this]; omega

lemma vsigma (q x n : ℕ) [Fact q.Prime] (hx : 1 < x) :
    padicValNat q (∑ i ∈ range (2*n+1), x^i) + padicValNat q (x - 1)
      = padicValNat q (x^(2*n+1) - 1) := by
  rw [← geom_nat x _ (by omega), padicValNat.mul (geom_ne x n) (by omega)]

lemma v_eq_one (q N : ℕ) [hq : Fact q.Prime] (h1 : N % q = 0) (h2 : (N / q) % q ≠ 0) :
    padicValNat q N = 1 := by
  have hN : N = q * (N / q) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h1)).symm
  have hq1 := hq.out.one_lt
  have hne : N / q ≠ 0 := by intro h; rw [h] at h2; simp at h2
  rw [hN, padicValNat.mul (by omega) hne, padicValNat.self hq1,
    padicValNat.eq_zero_of_not_dvd (fun h => h2 (Nat.mod_eq_zero_of_dvd h))]

lemma prime_dvd_four (r A B C E : ℕ) (hr : r.Prime) (h : r ∣ A * B * C * E) (hA : ¬ r ∣ A)
    (hB : ¬ r ∣ B) (hC : ¬ r ∣ C) (hE : ¬ r ∣ E) : False := by
  rcases (hr.dvd_mul).mp h with h | h
  · rcases (hr.dvd_mul).mp h with h | h
    · rcases (hr.dvd_mul).mp h with h | h
      · exact hA h
      · exact hB h
    · exact hC h
  · exact hE h

lemma final_ineq (b c e : ℕ) (he : 2 ≤ e) (h5 : 5^(2*b) ≤ 5*(2*e+1))
    (h19 : 19^(2*c) ≤ 19^3*(2*b+1)*(2*e+1))
    (h101 : 101^(2*e) ≤ 101^2*(2*b+1)*(2*c+1)) : False := by
  have hb : b ≤ e := by
    by_contra hbe
    have h1 : 2*e+1 < 5^(2*e+1) := Nat.lt_pow_self (by norm_num)
    have h2 : 5^(2*e+2) ≤ 5^(2*b) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ] at h2
    omega
  have hc : c ≤ e + 1 := by
    by_contra hce
    have h1 : 2*e+1 < 4^(2*e+1) := Nat.lt_pow_self (by norm_num)
    have h1' : (2*e+1)*(2*e+1) < 4^(2*e+1) * 4^(2*e+1) := Nat.mul_lt_mul'' h1 h1
    rw [← mul_pow] at h1'
    have h3 : (4*4)^(2*e+1) ≤ 19^(2*e+1) := Nat.pow_le_pow_left (by norm_num) _
    have h2 : 19^(2*e+4) ≤ 19^(2*c) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [show 2*e+4 = 3 + (2*e+1) by ring, pow_add] at h2
    have h4 : (2*b+1)*(2*e+1) ≤ (2*e+1)*(2*e+1) := Nat.mul_le_mul_right _ (by omega)
    have h5' : 19^3*(2*b+1)*(2*e+1) ≤ 19^3 * ((2*e+1)*(2*e+1)) := by
      rw [mul_assoc]; exact Nat.mul_le_mul_left _ h4
    have : 19^3 * 19^(2*e+1) ≤ 19^3 * ((2*e+1)*(2*e+1)) := le_trans h2 (le_trans h19 h5')
    have := Nat.le_of_mul_le_mul_left this (by norm_num)
    omega
  obtain ⟨f, rfl⟩ : ∃ f, e = f + 2 := ⟨e - 2, by omega⟩
  have hf : f < 101^f := Nat.lt_pow_self (by norm_num)
  set Y := 101^f with hY
  have hpow : 101^(2*(f+2)) = 101^2 * (101 * Y) * (101 * Y) := by
    rw [hY]; ring
  rw [hpow] at h101
  have hY' : 2*f + 7 < 101 * Y := by omega
  have hBC : (2*b+1)*(2*c+1) ≤ (2*f+7)*(2*f+7) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hlt : (2*f+7)*(2*f+7) < (101*Y)*(101*Y) := Nat.mul_lt_mul'' hY' hY'
  have : 101^2 * ((101*Y)*(101*Y)) ≤ 101^2 * ((2*f+7)*(2*f+7)) := by
    calc 101^2 * ((101*Y)*(101*Y)) = 101^2 * (101 * Y) * (101 * Y) := by ring
      _ ≤ 101^2*(2*b+1)*(2*c+1) := h101
      _ = 101^2*((2*b+1)*(2*c+1)) := by ring
      _ ≤ 101^2 * ((2*f+7)*(2*f+7)) := Nat.mul_le_mul_left _ hBC
  have := Nat.le_of_mul_le_mul_left this (by norm_num)
  omega

end OPN4afa

theorem solution (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hcase : ((D < 225 ∧ Odd D ∧ p.Prime ∧ p = 2 * D - 1 ∧ q4.Prime ∧ 19 < q4 ∧ D < q4 ∧ (∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 19 ∨ r = q4) ∧ 4 ≤ a ∧ 3 ≤ b ∧ 2 ≤ c ∧ 1 ≤ e ∧ ((D = 57 ∧ 580 ≤ q4 ∧ q4 ≤ 602) ∨ (D = 75 ∧ 261 ≤ q4 ∧ q4 ≤ 264) ∨ (D = 135 ∧ 146 ≤ q4 ∧ q4 ≤ 148))) ∨ (D = 855 ∧ q4 = 101 ∧ 1 ≤ e))) : False := by
  have hm2 : m ^ 2 ∣ D * sigma := ⟨p, by rw [hrel]; ring⟩
  have hS3 := OPN4afa.geom_ne 3 a
  have hS5 := OPN4afa.geom_ne 5 b
  have hS19 := OPN4afa.geom_ne 19 c
  have hSq := OPN4afa.geom_ne q4 e
  have hsig0 : sigma ≠ 0 := by
    rw [hsigma]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero hS3 hS5) hS19) hSq
  have h5pow : 5^(2*b) ∣ m^2 := by
    rw [hfac]; exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_mul_left _ _) _) _
  have h19pow : 19^(2*c) ∣ m^2 := by
    rw [hfac]; exact Dvd.dvd.mul_right (dvd_mul_left _ _) _
  have hqpow : q4^(2*e) ∣ m^2 := by
    rw [hfac]; exact dvd_mul_left _ _
  have hodd : ∀ n : ℕ, (2*n+1) % 2 = 1 := fun n => by omega
  have n5_3 : ¬ 5 ∣ ∑ i ∈ Finset.range (2*a+1), 3^i :=
    OPN4afa.not_dvd_geom 5 3 4 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by decide) (hodd a)
  have n5_5 : ¬ 5 ∣ ∑ i ∈ Finset.range (2*b+1), 5^i := OPN4afa.not_self_dvd 5 (2*b) (by norm_num)
  have n5_19 : ¬ 5 ∣ ∑ i ∈ Finset.range (2*c+1), 19^i :=
    OPN4afa.not_dvd_geom 5 19 2 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by decide) (hodd c)
  rcases hcase with ⟨_, _, _, hpeq, hq4p, _, _, _, _, hb, _, _, hsub⟩ | ⟨hD, hq4, he⟩
  · have h5m : 5 ∣ m^2 := dvd_trans (dvd_pow_self 5 (by omega : 2*b ≠ 0)) h5pow
    rcases hsub with ⟨rfl, hlo, hhi⟩ | ⟨rfl, hlo, hhi⟩ | ⟨rfl, hlo, hhi⟩
    · -- D = 57, p = 113
      norm_num at hpeq; subst hpeq
      have hmem : q4 = 587 ∨ q4 = 593 ∨ q4 = 599 ∨ q4 = 601 := by
        interval_cases q4 <;> first | (norm_num at hq4p; done) | decide
      have h5s : 5 ∣ sigma := by
        have h : 5 ∣ 57 * sigma := by rw [hrel]; exact Dvd.dvd.mul_left h5m _
        omega
      have h113 : 113 ∣ sigma := by
        have h : 113 ∣ 57 * sigma := by rw [hrel]; exact dvd_mul_right _ _
        omega
      rw [hsigma] at h5s h113
      rcases hmem with rfl | rfl | rfl | rfl
      · exact OPN4afa.prime_dvd_four 5 _ _ _ _ (by norm_num) h5s n5_3 n5_5 n5_19
          (OPN4afa.not_dvd_geom 5 587 4 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by decide) (hodd e))
      · exact OPN4afa.prime_dvd_four 5 _ _ _ _ (by norm_num) h5s n5_3 n5_5 n5_19
          (OPN4afa.not_dvd_geom 5 593 4 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by decide) (hodd e))
      · exact OPN4afa.prime_dvd_four 5 _ _ _ _ (by norm_num) h5s n5_3 n5_5 n5_19
          (OPN4afa.not_dvd_geom 5 599 2 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by decide) (hodd e))
      · exact OPN4afa.prime_dvd_four 113 _ _ _ _ (by norm_num) h113
          (OPN4afa.not_dvd_geom 113 3 112 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by decide) (hodd a))
          (OPN4afa.not_dvd_geom 113 5 112 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by decide) (hodd b))
          (OPN4afa.not_dvd_geom 113 19 112 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by decide) (hodd c))
          (OPN4afa.not_dvd_geom 113 601 112 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by decide) (hodd e))
    · -- D = 75, p = 149
      have hq : q4 = 263 := by
        interval_cases q4 <;> first | (norm_num at hq4p; done) | decide
      subst hq
      have h5s : 5 ∣ sigma := by
        have h : 5^3 ∣ 75 * sigma := by
          rw [hrel]; exact Dvd.dvd.mul_left (dvd_trans (pow_dvd_pow 5 (by omega)) h5pow) _
        norm_num at h
        omega
      rw [hsigma] at h5s
      exact OPN4afa.prime_dvd_four 5 _ _ _ _ (by norm_num) h5s n5_3 n5_5 n5_19
        (OPN4afa.not_dvd_geom 5 263 4 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by decide) (hodd e))
    · -- D = 135
      interval_cases q4 <;> norm_num at hq4p
  · -- D = 855, q4 = 101
    subst hD hq4
    have : Fact (Nat.Prime 101) := ⟨by norm_num⟩
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    have hN : 855 * sigma ≠ 0 := mul_ne_zero (by norm_num) hsig0
    have hsplit : ∀ (r : ℕ) [Fact r.Prime], padicValNat r (855 * sigma) =
        padicValNat r 855 + padicValNat r (∑ i ∈ Finset.range (2*a+1), 3^i)
        + padicValNat r (∑ i ∈ Finset.range (2*b+1), 5^i)
        + padicValNat r (∑ i ∈ Finset.range (2*c+1), 19^i)
        + padicValNat r (∑ i ∈ Finset.range (2*e+1), 101^i) := by
      intro r _
      rw [hsigma, padicValNat.mul (by norm_num)
          (mul_ne_zero (mul_ne_zero (mul_ne_zero hS3 hS5) hS19) hSq),
        padicValNat.mul (mul_ne_zero (mul_ne_zero hS3 hS5) hS19) hSq,
        padicValNat.mul (mul_ne_zero hS3 hS5) hS19, padicValNat.mul hS3 hS5]
      ring
    have hv101 : 2*e ≤ padicValNat 101 (855 * sigma) :=
      (padicValNat_dvd_iff_le hN).mp (dvd_trans hqpow hm2)
    have hv5 : 2*b ≤ padicValNat 5 (855 * sigma) :=
      (padicValNat_dvd_iff_le hN).mp (dvd_trans h5pow hm2)
    have hv19 : 2*c ≤ padicValNat 19 (855 * sigma) :=
      (padicValNat_dvd_iff_le hN).mp (dvd_trans h19pow hm2)
    rw [hsplit] at hv101 hv5 hv19
    -- 101-adic facts
    have a1 : padicValNat 101 855 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
    have a2 : padicValNat 101 (∑ i ∈ Finset.range (2*a+1), 3^i) = 0 :=
      padicValNat.eq_zero_of_not_dvd (OPN4afa.not_dvd_geom 101 3 100 _ (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by decide) (hodd a))
    have a3 : padicValNat 101 (∑ i ∈ Finset.range (2*e+1), 101^i) = 0 :=
      padicValNat.eq_zero_of_not_dvd (OPN4afa.not_self_dvd 101 (2*e) (by norm_num))
    have a4 := OPN4afa.vsigma 101 5 b (by norm_num)
    have a5 := OPN4afa.vbound 101 5 25 (2*b+1) 1 ⟨50, by norm_num⟩ (by norm_num) (by norm_num)
      (by norm_num) (OPN4afa.v_eq_one 101 _ (by norm_num) (by norm_num)) (by decide)
    have a6 : padicValNat 101 (5 - 1) = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
    have a7 := OPN4afa.vsigma 101 19 c (by norm_num)
    have a8 := OPN4afa.vbound 101 19 25 (2*c+1) 1 ⟨50, by norm_num⟩ (by norm_num) (by norm_num)
      (by norm_num) (OPN4afa.v_eq_one 101 _ (by norm_num) (by norm_num)) (by decide)
    have a9 : padicValNat 101 (19 - 1) = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
    have aB : 101 ^ padicValNat 101 (2*b+1) ≤ 2*b+1 := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
    have aC : 101 ^ padicValNat 101 (2*c+1) ≤ 2*c+1 := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
    -- 5-adic facts
    have v100 : padicValNat 5 100 = 2 := by
      rw [show (100:ℕ) = 5 * 20 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
        padicValNat.self (by norm_num), OPN4afa.v_eq_one 5 20 (by norm_num) (by norm_num)]
    have b1 : padicValNat 5 855 = 1 := OPN4afa.v_eq_one 5 855 (by norm_num) (by norm_num)
    have b2 : padicValNat 5 (∑ i ∈ Finset.range (2*a+1), 3^i) = 0 :=
      padicValNat.eq_zero_of_not_dvd n5_3
    have b3 : padicValNat 5 (∑ i ∈ Finset.range (2*b+1), 5^i) = 0 :=
      padicValNat.eq_zero_of_not_dvd n5_5
    have b4 : padicValNat 5 (∑ i ∈ Finset.range (2*c+1), 19^i) = 0 :=
      padicValNat.eq_zero_of_not_dvd n5_19
    have b5 := OPN4afa.vsigma 5 101 e (by norm_num)
    have b6 := OPN4afa.vbound 5 101 1 (2*e+1) 2 ⟨2, by norm_num⟩ (by norm_num) (by norm_num)
      (by norm_num) (by simpa using v100) (by intro r hr hr0; omega)
    have b7 : padicValNat 5 (101 - 1) = 2 := v100
    have bE : 5 ^ padicValNat 5 (2*e+1) ≤ 2*e+1 := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
    -- 19-adic facts
    have c1 : padicValNat 19 855 = 1 := OPN4afa.v_eq_one 19 855 (by norm_num) (by norm_num)
    have c2 : padicValNat 19 (∑ i ∈ Finset.range (2*a+1), 3^i) = 0 :=
      padicValNat.eq_zero_of_not_dvd (OPN4afa.not_dvd_geom 19 3 18 _ (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by decide) (hodd a))
    have c3 : padicValNat 19 (∑ i ∈ Finset.range (2*c+1), 19^i) = 0 :=
      padicValNat.eq_zero_of_not_dvd (OPN4afa.not_self_dvd 19 (2*c) (by norm_num))
    have c4 := OPN4afa.vsigma 19 5 b (by norm_num)
    have c5 := OPN4afa.vbound 19 5 9 (2*b+1) 1 ⟨9, by norm_num⟩ (by norm_num) (by norm_num)
      (by norm_num) (OPN4afa.v_eq_one 19 _ (by norm_num) (by norm_num)) (by decide)
    have c6 : padicValNat 19 (5 - 1) = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
    have c7 := OPN4afa.vsigma 19 101 e (by norm_num)
    have c8 := OPN4afa.vbound 19 101 9 (2*e+1) 1 ⟨9, by norm_num⟩ (by norm_num) (by norm_num)
      (by norm_num) (OPN4afa.v_eq_one 19 _ (by norm_num) (by norm_num)) (by decide)
    have c9 : padicValNat 19 (101 - 1) = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
    have cB : 19 ^ padicValNat 19 (2*b+1) ≤ 2*b+1 := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
    have cE : 19 ^ padicValNat 19 (2*e+1) ≤ 2*e+1 := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
    -- abstract
    generalize padicValNat 101 (∑ i ∈ Finset.range (2*b+1), 5^i) = V5 at *
    generalize padicValNat 101 (∑ i ∈ Finset.range (2*c+1), 19^i) = V19 at *
    generalize padicValNat 101 (2*b+1) = xB at *
    generalize padicValNat 101 (2*c+1) = xC at *
    generalize padicValNat 5 (2*e+1) = z at *
    generalize padicValNat 19 (2*b+1) = u at *
    generalize padicValNat 19 (2*e+1) = w at *
    have hb5 : 2*b ≤ 1 + z := by omega
    have hc19 : 2*c ≤ 3 + u + w := by omega
    rcases Nat.lt_or_ge e 2 with he1 | he2
    · -- e = 1
      have he1' : e = 1 := by omega
      subst he1'
      have hz : z = 0 := by
        by_contra hz
        have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 5) (Nat.one_le_iff_ne_zero.mpr hz)
        omega
      have hb0 : b = 0 := by omega
      subst hb0
      have hu : u = 0 := by
        by_contra hu
        have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 19) (Nat.one_le_iff_ne_zero.mpr hu)
        omega
      have hw : w = 0 := by
        by_contra hw
        have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 19) (Nat.one_le_iff_ne_zero.mpr hw)
        omega
      have hc1 : c ≤ 1 := by omega
      have hV5 : V5 = 0 := by
        have : V5 + 0 ≤ 1 + xB := by
          rw [a4.symm.trans rfl] at a5
          omega
        -- b = 0 means the sum is 1
        have hx : xB = 0 := by
          by_contra hx
          have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 101) (Nat.one_le_iff_ne_zero.mpr hx)
          omega
        have hsum : padicValNat 101 (5 ^ (2*0+1) - 1) = 0 :=
          padicValNat.eq_zero_of_not_dvd (by norm_num)
        omega
      have hV19 : V19 = 0 := by
        interval_cases c
        · have hsum : padicValNat 101 (19 ^ (2*0+1) - 1) = 0 :=
            padicValNat.eq_zero_of_not_dvd (by norm_num)
          omega
        · have hsum : padicValNat 101 (19 ^ (2*1+1) - 1) = 0 :=
            padicValNat.eq_zero_of_not_dvd (by norm_num)
          omega
      omega
    · -- e ≥ 2
      have h5' : 5^(2*b) ≤ 5*(2*e+1) := by
        calc 5^(2*b) ≤ 5^(1+z) := Nat.pow_le_pow_right (by norm_num) hb5
          _ = 5 * 5^z := by rw [pow_add, pow_one]
          _ ≤ 5*(2*e+1) := Nat.mul_le_mul_left _ bE
      have h19' : 19^(2*c) ≤ 19^3*(2*b+1)*(2*e+1) := by
        calc 19^(2*c) ≤ 19^(3+u+w) := Nat.pow_le_pow_right (by norm_num) hc19
          _ = 19^3 * 19^u * 19^w := by rw [pow_add, pow_add]
          _ ≤ 19^3*(2*b+1)*(2*e+1) := Nat.mul_le_mul (Nat.mul_le_mul_left _ cB) cE
      have h2e : 2*e ≤ 2 + xB + xC := by omega
      have h101' : 101^(2*e) ≤ 101^2*(2*b+1)*(2*c+1) := by
        calc 101^(2*e) ≤ 101^(2+xB+xC) := Nat.pow_le_pow_right (by norm_num) h2e
          _ = 101^2 * 101^xB * 101^xC := by rw [pow_add, pow_add]
          _ ≤ 101^2*(2*b+1)*(2*c+1) := Nat.mul_le_mul (Nat.mul_le_mul_left _ aB) aC
      exact OPN4afa.final_ineq b c e he2 h5' h19' h101'
