-- Prove2me | solution 1 for OddPerfectNumber.sigma_prime_pow_ne_two_mul_sq_of_six_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-08T21:03:08.359184+00:00
-- url     : https://prove2.me/submissions/97b144af-1352-4e2a-9ce3-ff4b4600e541

import Mathlib

open Finset

private lemma sigma_pp {p : ℕ} (hp : p.Prime) (a : ℕ) :
    (∑ d ∈ (p ^ a).divisors, d) = ∑ i ∈ range (a + 1), p ^ i :=
  Nat.sum_divisors_prime_pow hp

private lemma sigma_pp_succ {p : ℕ} (hp : p.Prime) (a : ℕ) :
    (∑ d ∈ (p ^ (a + 1)).divisors, d) = p * (∑ d ∈ (p ^ a).divisors, d) + 1 := by
  rw [sigma_pp hp, sigma_pp hp, geom_sum_succ]

private lemma sigma_pp_geom {p : ℕ} (hp : p.Prime) (a : ℕ) :
    (p - 1) * (∑ d ∈ (p ^ a).divisors, d) + 1 = p ^ (a + 1) := by
  obtain ⟨c, rfl⟩ : ∃ c, p = c + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
  simp only [Nat.add_sub_cancel]
  induction a with
  | zero => simp
  | succ a ih =>
      rw [sigma_pp_succ hp]
      have h : c * ((c + 1) * (∑ d ∈ ((c + 1) ^ a).divisors, d) + 1) + 1
          = (c + 1) * (c * (∑ d ∈ ((c + 1) ^ a).divisors, d) + 1) := by ring
      rw [h, ih]
      ring

private lemma sigma_pp_mod_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (e : ℕ) :
    (∑ d ∈ (p ^ e).divisors, d) % 2 = (e + 1) % 2 := by
  have hp1 : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  induction e with
  | zero => simp
  | succ e ih =>
      rw [sigma_pp_succ hp]
      have hm := Nat.mul_mod p (∑ d ∈ (p ^ e).divisors, d) 2
      rw [hp1, one_mul, Nat.mod_mod_of_dvd] at hm
      · omega
      · exact dvd_rfl

private lemma not_sq_quad {t d : ℕ} (ht : 1 ≤ t) : t ^ 2 + t + 1 ≠ d ^ 2 := by
  intro h
  rcases le_or_gt d t with hd | hd
  · have : d ^ 2 ≤ t ^ 2 := Nat.pow_le_pow_left hd 2
    omega
  · have hd1 : t + 1 ≤ d := hd
    have h2 : (t + 1) ^ 2 ≤ d ^ 2 := Nat.pow_le_pow_left hd1 2
    have h3 : (t + 1) ^ 2 = t ^ 2 + 2 * t + 1 := by ring
    omega

/-- For an odd prime `p` and an exponent `k` with `6 ∣ k + 1`, the equation
`σ (p ^ k) = 2 m ^ 2` has no solution. -/
theorem solution (p k m : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hk : (k + 1) % 6 = 0) :
    (∑ d ∈ (p ^ k).divisors, d) ≠ 2 * m ^ 2 := by
  intro hsq
  obtain ⟨w, hw⟩ : ∃ w, k + 1 = 6 * w := ⟨(k + 1) / 6, by omega⟩
  have hw1 : 1 ≤ w := by omega
  have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hWgeom : (p - 1) * (∑ d ∈ (p ^ (2 * w - 1)).divisors, d) + 1 = (p ^ w) ^ 2 := by
    have h := sigma_pp_geom hp (2 * w - 1)
    rw [show 2 * w - 1 + 1 = 2 * w by omega] at h
    rw [h, ← pow_mul, mul_comm w 2]
  have hkgeom : (p - 1) * (∑ d ∈ (p ^ k).divisors, d) + 1 = (p ^ w) ^ 6 := by
    have h := sigma_pp_geom hp k
    rw [hw] at h
    rw [h, ← pow_mul, mul_comm w 6]
  have hpwodd : (p ^ w) % 2 = 1 := by
    have hnd : ¬ (2 ∣ p ^ w) := by
      intro hdvd
      have h2p : (2 : ℕ) ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdvd
      have := hp.eq_one_or_self_of_dvd 2 h2p
      omega
    omega
  have hpw3 : 3 ≤ p ^ w := by
    calc 3 ≤ p := hp3
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ w := Nat.pow_le_pow_right (by omega) hw1
  obtain ⟨A, hA⟩ : ∃ A, A = p - 1 := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = ∑ d ∈ (p ^ (2 * w - 1)).divisors, d := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ d ∈ (p ^ k).divisors, d := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = p ^ w := ⟨_, rfl⟩
  rw [← hA, ← hW, ← hy] at hWgeom
  rw [← hA, ← hS, ← hy] at hkgeom
  rw [← hS] at hsq
  rw [← hy] at hpwodd hpw3
  have hA2 : 2 ≤ A := by omega
  obtain ⟨e, he⟩ : ∃ e, y = e + 2 := ⟨y - 2, by omega⟩
  subst he
  have he1 : 1 ≤ e := by omega
  have hepar : e % 2 = 1 := by omega
  obtain ⟨V, hV⟩ : ∃ V, V = A * W := ⟨_, rfl⟩
  rw [← hV] at hWgeom
  have hsqe : (e + 2) ^ 2 = e ^ 2 + 4 * e + 4 := by ring
  have hVe : V = e ^ 2 + 4 * e + 3 := by omega
  have hPsi : (e + 2) ^ 4 + (e + 2) ^ 2 + 1 = V ^ 2 + 3 * V + 3 := by rw [hVe]; ring
  have hy6 : (e + 2) ^ 6 = (V + 1) ^ 3 := by rw [hVe]; ring
  have hfact : S = W * ((e + 2) ^ 4 + (e + 2) ^ 2 + 1) := by
    have h1 : A * (W * ((e + 2) ^ 4 + (e + 2) ^ 2 + 1)) = V * (V ^ 2 + 3 * V + 3) := by
      rw [hPsi, hV]; ring
    have h2 : A * S + 1 = (V + 1) ^ 3 := by rw [hkgeom, hy6]
    have h3 : V * (V ^ 2 + 3 * V + 3) + 1 = (V + 1) ^ 3 := by ring
    have hcancel : A * S = A * (W * ((e + 2) ^ 4 + (e + 2) ^ 2 + 1)) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega) hcancel
  obtain ⟨W', hW'⟩ : (2 : ℕ) ∣ W := by
    have := sigma_pp_mod_two hp hp2 (2 * w - 1)
    rw [← hW] at this
    omega
  obtain ⟨B, hB⟩ : ∃ B, B = e ^ 2 + 5 * e + 7 := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = e ^ 2 + 3 * e + 3 := ⟨_, rfl⟩
  have hBC : B * C = (e + 2) ^ 4 + (e + 2) ^ 2 + 1 := by rw [hB, hC]; ring
  have hkey : W' * (B * C) = m ^ 2 := by
    have h1 : 2 * (W' * (B * C)) = 2 * m ^ 2 := by
      rw [hBC, ← hsq, hfact, hW']; ring
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h1
  have hW'V : W' ∣ V := by
    have h1 : W' ∣ W := ⟨2, by omega⟩
    have h2 : W ∣ V := ⟨A, by rw [hV]; ring⟩
    exact h1.trans h2
  have hgcdB : ∀ d : ℕ, d ∣ B → d ∣ V → d ∣ 3 := by
    intro d hdB hdV
    have h1 : d ∣ e + 4 := by
      refine (Nat.dvd_add_right hdV).mp ?_
      rwa [show V + (e + 4) = B by omega]
    have h2 : d ∣ (e + 4) * e := h1.mul_right e
    refine (Nat.dvd_add_right h2).mp ?_
    rwa [show (e + 4) * e + 3 = V by rw [hVe]; ring]
  have hgcdC : ∀ d : ℕ, d ∣ C → d ∣ V → d ∣ 3 := by
    intro d hdC hdV
    have h1 : d ∣ e := by
      refine (Nat.dvd_add_right hdC).mp ?_
      rwa [show C + e = V by omega]
    have h2 : d ∣ e ^ 2 + 3 * e := by
      have hsq2 : d ∣ e ^ 2 := by rw [pow_two]; exact h1.mul_left e
      exact dvd_add hsq2 (h1.mul_left 3)
    refine (Nat.dvd_add_right h2).mp ?_
    rwa [show e ^ 2 + 3 * e + 3 = C by omega]
  obtain ⟨f, hf⟩ : ∃ f, e = 2 * f + 1 := ⟨e / 2, by omega⟩
  have hBodd : B % 2 = 1 := by
    have hB2 : B = 4 * f ^ 2 + 14 * f + 13 := by rw [hB, hf]; ring
    omega
  have hcopBC : Nat.Coprime B C := by
    have hg := Nat.gcd_dvd_left B C
    have hg' := Nat.gcd_dvd_right B C
    have hdy : Nat.gcd B C ∣ (e + 2) * 2 := by
      refine (Nat.dvd_add_right hg').mp ?_
      rwa [show C + (e + 2) * 2 = B by rw [hB, hC]; ring]
    have hgodd : ¬ (2 ∣ Nat.gcd B C) := by
      intro hev
      have : (2 : ℕ) ∣ B := hev.trans hg
      omega
    have hcop2 : Nat.Coprime (Nat.gcd B C) 2 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hgodd).symm
    have hdye : Nat.gcd B C ∣ e + 2 := hcop2.dvd_of_dvd_mul_right hdy
    have h1 : Nat.gcd B C ∣ (e + 2) * (e + 3) := hdye.mul_right _
    have h2 : Nat.gcd B C ∣ 1 := by
      refine (Nat.dvd_add_right h1).mp ?_
      rwa [show (e + 2) * (e + 3) + 1 = B by rw [hB]; ring]
    exact Nat.dvd_one.mp h2
  have h3BC : ¬ ((3 : ℕ) ∣ B ∧ (3 : ℕ) ∣ C) := by
    rintro ⟨hb, hc⟩
    have hd : (3 : ℕ) ∣ Nat.gcd B C := Nat.dvd_gcd hb hc
    rw [hcopBC] at hd
    omega
  rcases Classical.em ((3 : ℕ) ∣ B) with hb3 | hb3
  · have hc3 : ¬ (3 : ℕ) ∣ C := fun hc => h3BC ⟨hb3, hc⟩
    have hcopCW : Nat.Coprime C W' := by
      have hg := Nat.gcd_dvd_left C W'
      have hg' := (Nat.gcd_dvd_right C W').trans hW'V
      rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ (hgcdC _ hg hg') with h | h
      · exact h
      · exact absurd (h ▸ hg) hc3
    have hcop : Nat.Coprime C (W' * B) := Nat.Coprime.mul_right hcopCW hcopBC.symm
    have heq : C * (W' * B) = m ^ 2 := by rw [← hkey]; ring
    obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr hcop) heq
    exact not_sq_quad (t := e + 1) (d := d) (by omega) (by rw [← hd, hC]; ring)
  · have hcopBW : Nat.Coprime B W' := by
      have hg := Nat.gcd_dvd_left B W'
      have hg' := (Nat.gcd_dvd_right B W').trans hW'V
      rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ (hgcdB _ hg hg') with h | h
      · exact h
      · exact absurd (h ▸ hg) hb3
    have hcop : Nat.Coprime B (W' * C) := Nat.Coprime.mul_right hcopBW hcopBC
    have heq : B * (W' * C) = m ^ 2 := by rw [← hkey]; ring
    obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr hcop) heq
    exact not_sq_quad (t := e + 2) (d := d) (by omega) (by rw [← hd, hB]; ring)

