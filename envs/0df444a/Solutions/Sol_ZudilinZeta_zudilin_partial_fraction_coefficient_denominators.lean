-- Prove2me | solution 1 for ZudilinZeta.zudilin_partial_fraction_coefficient_denominators
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-01T14:36:40.854549+00:00
-- url     : https://prove2.me/submissions/ee5947a4-4d3c-4bec-a7f0-f069f3fbfb9c

import Definitions.Def_ZudilinZetaCoefficientArithmetic
import Theorems.Thm_ZudilinZeta_zudilin_partial_fraction_rough_denominators
import Theorems.Thm_ZudilinZeta_zudilin_partial_fraction_prime_bound

set_option autoImplicit false

open Finset ZudilinZeta

private lemma cd_prime_product_dvd (T : Finset ℕ) (e : ℕ → ℤ) (a : ℤ)
    (hprime : ∀ p ∈ T, p.Prime)
    (hv : ∀ p ∈ T, e p ≤ padicValRat p (a : ℚ)) :
    ((∏ p ∈ T, p^(e p).toNat : ℕ) : ℤ) ∣ a := by
  classical
  rw [Nat.cast_prod]
  apply Finset.prod_dvd_of_coprime
  · intro p hp q hq hpq
    exact (Nat.coprime_pow_primes _ _ (hprime p hp) (hprime q hq) hpq).isCoprime
  · intro p hp
    rw [Nat.cast_pow, padicValInt_dvd_iff_of_ne_one (hprime p hp).ne_one]
    right
    apply Int.toNat_le.mpr
    simpa only [padicValRat.of_int] using hv p hp

private lemma cd_eta_mono (P : Params) {i j : ℕ} (hi : 1 ≤ i)
    (hij : i ≤ j) (hj : j ≤ P.q) : P.eta i ≤ P.eta j := by
  have hstep (k : ℕ) : ∀ i, 1 ≤ i → i+k ≤ P.q → P.eta i ≤ P.eta (i+k) := by
    induction k with
    | zero => intro i _ _; simp
    | succ k ih =>
      intro i hi hik
      have h₁ := ih i hi (by omega)
      have h₂ := P.eta_mono (i+k) (mem_Ico.mpr ⟨by omega, by omega⟩)
      simpa only [Nat.succ_eq_add_one, ← add_assoc] using h₁.trans h₂
  simpa only [Nat.add_sub_of_le hij] using hstep (j-i) i hi (by omega)

private lemma cd_m_antitone (P : Params) {i j : ℕ} (hi : 1 ≤ i)
    (hij : i ≤ j) (hj : j ≤ P.q-P.r) : m P j ≤ m P i := by
  have hrq := P.q_ge
  have he := cd_eta_mono P (i := P.r+i) (j := P.r+j) (by omega) (by omega) (by omega)
  unfold m
  exact max_le_max le_rfl (max_le_max le_rfl (Nat.sub_le_sub_left he _))

private lemma cd_m_le_eta0 (P : Params) (j : ℕ) : m P j ≤ P.eta 0 := by
  have hrq := P.q_ge
  have hr : 1 ≤ P.r := P.r_odd.pos
  have he := cd_eta_mono P hr (by omega : P.r ≤ P.q) le_rfl
  have he0 := P.eta_lt
  unfold m
  apply max_le (by omega)
  exact max_le (Nat.sub_le _ _) ((Nat.sub_le _ _).trans (Nat.sub_le _ _))

private lemma cd_base_le_m (P : Params) (j : ℕ) :
    max (P.eta P.r) (P.eta 0-2*P.eta (P.r+1)) ≤ m P j :=
  max_le (le_max_left _ _) ((le_max_left _ _).trans (le_max_right _ _))

private lemma cd_D_dvd {A B : ℕ} (h : A ≤ B) : D A ∣ D B := by
  apply Finset.lcm_dvd
  intro k hk
  apply Finset.dvd_lcm (f := id)
  exact mem_Icc.mpr ⟨(mem_Icc.mp hk).1, (mem_Icc.mp hk).2.trans h⟩

private lemma cd_D_val_one (p N : ℕ) (hp : p.Prime) (hpN : p ≤ N) (hNp : N < p*p) :
    padicValRat p (D N : ℚ) = 1 := by
  rw [padicValRat.of_nat, ← Nat.factorization_def _ hp]
  change ((Nat.lcmUpto N).factorization p : ℤ) = 1
  rw [Nat.factorization_lcmUpto N hp, Nat.log_eq_one_iff'.mpr ⟨hpN, hNp⟩]
  norm_num

private lemma cd_tail_nonzero (P : Params) (n s : ℕ) :
    (∏ j ∈ Icc (s+1) (P.q-P.r), D (m P j*n)) ≠ 0 := by
  apply prod_ne_zero_iff.mpr
  intro j hj
  exact Nat.lcmUpto_ne_zero _

private lemma cd_tail_rough_dvd (P : Params) (n s : ℕ) (hs : s ≤ P.q-P.r) :
    (D (max (P.eta P.r) (P.eta 0-2*P.eta (P.r+1))*n))^(P.q-P.r-s) ∣
      ∏ j ∈ Icc (s+1) (P.q-P.r), D (m P j*n) := by
  have hd (j : ℕ) (hj : j ∈ Icc (s+1) (P.q-P.r)) :
      D (max (P.eta P.r) (P.eta 0-2*P.eta (P.r+1))*n) ∣ D (m P j*n) :=
    cd_D_dvd (Nat.mul_le_mul_right n (cd_base_le_m P j))
  have h := Finset.prod_dvd_prod_of_dvd _ _ hd
  simpa only [prod_const, Nat.card_Icc, Nat.add_sub_add_right] using h

private lemma cd_tail_valuation (P : Params) (n s p : ℕ)
    (hs : s ≤ P.q-P.r) (hp : p.Prime) (hpmax : p ≤ m P (P.q-P.r)*n)
    (hcut : P.eta 0*n < p*p) :
    padicValRat p ((∏ j ∈ Icc (s+1) (P.q-P.r), D (m P j*n) : ℕ) : ℚ) =
      ((P.q-P.r-s : ℕ) : ℤ) := by
  have he (j : ℕ) (hj : j ∈ Icc (s+1) (P.q-P.r)) :
      (D (m P j*n)).factorization p = 1 := by
    have hj' := mem_Icc.mp hj
    have hv := cd_D_val_one p (m P j*n) hp
      (hpmax.trans (Nat.mul_le_mul_right n (cd_m_antitone P (by omega) hj'.2 le_rfl)))
      ((Nat.mul_le_mul_right n (cd_m_le_eta0 P j)).trans_lt hcut)
    rw [padicValRat.of_nat, ← Nat.factorization_def _ hp] at hv
    exact_mod_cast hv
  rw [padicValRat.of_nat, ← Nat.factorization_def _ hp,
    Nat.factorization_prod_apply (g := fun j => D (m P j*n))
      (fun j hj => (Nat.lcmUpto_ne_zero (m P j*n) : D (m P j*n) ≠ 0))]
  rw [Finset.sum_congr rfl he]
  simp only [sum_const, smul_eq_mul, mul_one, Nat.card_Icc, Nat.add_sub_add_right]

theorem solution (P : Params) (n : ℕ) (hn : 0 < n) (d : PartialFractionData P n) :
    ∀ s ∈ Icc 1 (P.q-P.r), ∀ k ∈ poleRange P n,
      ∃ a : ℤ, tailDenominatorScale P n s*d.coeff s k = (a : ℚ) := by
  classical
  intro s hs k hk
  by_cases hc0 : d.coeff s k = 0
  · exact ⟨0, by simp [hc0]⟩
  let B : ℕ := ∏ j ∈ Icc (s+1) (P.q-P.r), D (m P j*n)
  have hB : B ≠ 0 := cd_tail_nonzero P n s
  have hBQ : (B : ℚ) ≠ 0 := by exact_mod_cast hB
  obtain ⟨a₀, ha₀⟩ := zudilin_partial_fraction_rough_denominators P n hn d s hs k hk
  obtain ⟨b, hb⟩ := cd_tail_rough_dvd P n s (mem_Icc.mp hs).2
  have hi : ∃ a : ℤ, (B : ℚ)*d.coeff s k = (a : ℚ) := by
    refine ⟨(b : ℤ)*a₀, ?_⟩
    dsimp only [B]
    rw [hb]
    push_cast
    rw [mul_right_comm, ha₀]
    ring
  obtain ⟨a, ha⟩ := hi
  let T := (Icc 1 (m P (P.q-P.r)*n)).filter (fun p => p.Prime ∧ P.eta 0*n < p*p)
  have hprime (p : ℕ) (hp : p ∈ T) : p.Prime := (mem_filter.mp hp).2.1
  have hv (p : ℕ) (hp : p ∈ T) : phi P ((n : ℝ)/(p : ℝ)) ≤ padicValRat p (a : ℚ) := by
    letI : Fact p.Prime := ⟨hprime p hp⟩
    have hp' := mem_filter.mp hp
    have hraw := zudilin_partial_fraction_prime_bound P n hn d s hs k hk hc0 p
      hp'.2.1 hp'.2.2 (mem_Icc.mp hp'.1).2
    have hBval := cd_tail_valuation P n s p (mem_Icc.mp hs).2 hp'.2.1
      (mem_Icc.mp hp'.1).2 hp'.2.2
    rw [← ha, padicValRat.mul hBQ hc0, hBval]
    omega
  have hdiv : (Phi P n : ℤ) ∣ a :=
    cd_prime_product_dvd T (fun p => phi P ((n : ℝ)/(p : ℝ))) a hprime hv
  obtain ⟨z, hz⟩ := hdiv
  refine ⟨z, ?_⟩
  have hPhi : Phi P n ≠ 0 := by
    apply prod_ne_zero_iff.mpr
    intro p hp
    exact pow_ne_zero _ (hprime p hp).ne_zero
  have hPhiQ : (Phi P n : ℚ) ≠ 0 := by exact_mod_cast hPhi
  have he : (B : ℚ)*d.coeff s k = (Phi P n : ℚ)*(z : ℚ) := by
    rw [ha, hz]
    push_cast
    rfl
  change (∏ j ∈ Icc (s+1) (P.q-P.r), (D (m P j*n) : ℚ))/(Phi P n : ℚ)*d.coeff s k = (z : ℚ)
  rw [← Nat.cast_prod]
  change (B : ℚ)/(Phi P n : ℚ)*d.coeff s k = (z : ℚ)
  rw [div_mul_eq_mul_div, he, mul_div_cancel_left₀ _ hPhiQ]
