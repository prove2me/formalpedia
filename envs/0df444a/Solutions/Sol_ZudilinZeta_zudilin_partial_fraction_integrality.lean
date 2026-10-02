-- Prove2me | solution 1 for ZudilinZeta.zudilin_partial_fraction_integrality
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-01T13:52:55.701547+00:00
-- url     : https://prove2.me/submissions/8d7a894f-d2e7-47e8-b139-594f6fec1b9d

import Theorems.Thm_ZudilinZeta_zudilin_partial_fraction_pole_support
import Theorems.Thm_ZudilinZeta_zudilin_partial_fraction_constant_shift
import Theorems.Thm_ZudilinZeta_zudilin_partial_fraction_coefficient_denominators

set_option autoImplicit false

open Finset
open ZudilinZeta

private lemma zz_integer_sum {ι : Type*} (S : Finset ι) (f : ι → ℚ)
    (h : ∀ x ∈ S, ∃ a : ℤ, f x = (a : ℚ)) :
    ∃ a : ℤ, ∑ x ∈ S, f x = (a : ℚ) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert x S hx ih =>
    obtain ⟨a, ha⟩ := h x (mem_insert_self _ _)
    obtain ⟨b, hb⟩ := ih (fun y hy => h y (mem_insert_of_mem hy))
    exact ⟨a+b, by simp only [sum_insert hx, ha, hb, Int.cast_add]⟩

private lemma zz_integer_mul {x y : ℚ} (hx : ∃ a : ℤ, x = (a : ℚ))
    (hy : ∃ a : ℤ, y = (a : ℚ)) : ∃ a : ℤ, x*y = (a : ℚ) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a*b, by simp⟩

private lemma zz_weight_integer (r s : ℕ) :
    ∃ a : ℤ, derivativeWeight r s = (a : ℚ) := by
  refine ⟨(s+(r-1)-1).choose (r-1), ?_⟩
  simp only [derivativeWeight, Nat.ascFactorial_eq_factorial_mul_choose', Nat.cast_mul]
  have h : ((r-1).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (r-1)
  simp [mul_div_cancel_left₀, h]

private lemma zz_eta_le (P : Params) {i j : ℕ} (hi : 1 ≤ i)
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

private lemma zz_m_antitone (P : Params) {i j : ℕ} (hi : 1 ≤ i)
    (hij : i ≤ j) (hj : j ≤ P.q-P.r) : m P j ≤ m P i := by
  have hrq := P.q_ge
  have he := zz_eta_le P (i := P.r+i) (j := P.r+j) (by omega) (by omega) (by omega)
  unfold m
  exact max_le_max le_rfl (max_le_max le_rfl (Nat.sub_le_sub_left he _))

private lemma zz_harmonic_bound (P : Params) (n s k : ℕ)
    (hs : s ∈ Icc 1 (P.q-P.r)) (hk : k ∈ orderPoleRange P n s) :
    k-hh P n 1 ≤ m P s*n := by
  have hrq := P.q_ge
  have hs' := mem_Icc.mp hs
  have hk' := (mem_Icc.mp hk).2
  have hj : P.r+s ≠ 0 := by omega
  have heta₁ := zz_eta_le P (i := 1) (j := P.q) (by omega) (by omega) le_rfl
  have heta₂ := zz_eta_le P (i := P.r+s) (j := P.q) (by omega) (by omega) le_rfl
  have he0 := P.eta_lt
  have he : P.eta 1 + P.eta (P.r+s) ≤ P.eta 0 := by omega
  have hnprod := Nat.mul_le_mul_right n he
  rw [Nat.add_mul] at hnprod
  have hm : P.eta 0-P.eta 1-P.eta (P.r+s) ≤ m P s :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hmn := Nat.mul_le_mul_right n hm
  have heq : (P.eta 0-P.eta 1-P.eta (P.r+s))*n =
      P.eta 0*n-P.eta 1*n-P.eta (P.r+s)*n := by rw [Nat.sub_mul, Nat.sub_mul]
  rw [show hh P n 0 = P.eta 0*n+2 by simp [hh],
    show hh P n (P.r+s) = P.eta (P.r+s)*n+1 by simp only [hh, if_neg hj]] at hk'
  simp only [hh, if_neg (by omega : (1 : ℕ) ≠ 0)]
  rw [heq] at hmn
  omega

private lemma zz_harmonic_power_dvd (P : Params) (n s l : ℕ)
    (hs : s ∈ Icc 1 (P.q-P.r)) (hl : 0 < l) (hls : l ≤ m P s*n) :
    l^(s+(P.r-1)) ∣ prefixClearing P n s := by
  have hs' := mem_Icc.mp hs
  have hr : 1 ≤ P.r := P.r_odd.pos
  have hd (j : ℕ) (hj : j ∈ Icc 1 s) : l ∣ D (m P j*n) := by
    apply Finset.dvd_lcm (f := id)
    exact mem_Icc.mpr ⟨hl, hls.trans (Nat.mul_le_mul_right n
      (zz_m_antitone P (mem_Icc.mp hj).1 (mem_Icc.mp hj).2 hs'.2))⟩
  have hprod : l^(s-1) ∣ ∏ j ∈ Icc 2 s, D (m P j*n) := by
    have hh : (∏ _j ∈ Icc 2 s, l) ∣ ∏ j ∈ Icc 2 s, D (m P j*n) :=
      Finset.prod_dvd_prod_of_dvd _ _ (fun j hj => hd j
        (mem_Icc.mpr ⟨by have := (mem_Icc.mp hj).1; omega, (mem_Icc.mp hj).2⟩))
    simpa only [prod_const, Nat.card_Icc, show s+1-2 = s-1 by omega] using hh
  have hpow := pow_dvd_pow_of_dvd (hd 1 (mem_Icc.mpr ⟨le_rfl, hs'.1⟩)) P.r
  have hexp : s+(P.r-1) = P.r+(s-1) := by omega
  rw [hexp, pow_add]
  exact Nat.mul_dvd_mul hpow hprod

private lemma zz_scale_factor (P : Params) (n s : ℕ)
    (hs : s ∈ Icc 1 (P.q-P.r)) :
    denominatorScale P n = (prefixClearing P n s : ℚ)*tailDenominatorScale P n s := by
  have hs' := mem_Icc.mp hs
  have hprod : (∏ j ∈ Icc 2 s, (D (m P j*n) : ℚ)) *
      (∏ j ∈ Icc (s+1) (P.q-P.r), (D (m P j*n) : ℚ)) =
      ∏ j ∈ Icc 2 (P.q-P.r), (D (m P j*n) : ℚ) := by
    simpa only [Ico_add_one_right_eq_Icc] using
      prod_Ico_consecutive (fun j => (D (m P j*n) : ℚ))
        (m := 2) (n := s+1) (k := P.q-P.r+1) (by omega) (by omega)
  simp only [denominatorScale, prefixClearing, tailDenominatorScale,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_prod]
  rw [← hprod]
  ring

private lemma zz_cleared_harmonic_integer (P : Params) (n s k : ℕ)
    (hs : s ∈ Icc 1 (P.q-P.r)) (hk : k ∈ orderPoleRange P n s) :
    ∃ a : ℤ, (prefixClearing P n s : ℚ) *
      (∑ l ∈ range (k-hh P n 1), (1 : ℚ)/((l : ℚ)+1)^(s+(P.r-1))) = (a : ℚ) := by
  rw [mul_sum]
  apply zz_integer_sum
  intro l hl
  have hbound : l+1 ≤ m P s*n := by
    have := mem_range.mp hl
    have := zz_harmonic_bound P n s k hs hk
    omega
  obtain ⟨b, hb⟩ := zz_harmonic_power_dvd P n s (l+1) hs (by omega) hbound
  refine ⟨b, ?_⟩
  rw [hb]
  push_cast
  have hne : (l : ℚ)+1 ≠ 0 := by positivity
  field_simp

theorem solution (P : Params) (n : ℕ) (hn : 0 < n)
    (d : PartialFractionData P n) :
    (∃ a : ℤ, denominatorScale P n*d.constantCoefficient = (a : ℚ)) ∧
      ∀ k ∈ Icc 1 ((P.q-P.r-2)/2),
        ∃ a : ℤ, denominatorScale P n*d.zetaCoefficient (2*k+1) = (a : ℚ) := by
  have hc := zudilin_partial_fraction_coefficient_denominators P n hn d
  constructor
  · rw [zudilin_partial_fraction_constant_shift P n hn d,
      PartialFractionData.shiftedConstantCoefficient, mul_neg, mul_sum]
    suffices hh : ∃ a : ℤ, (∑ s ∈ Icc 1 (P.q-P.r), denominatorScale P n *
        (derivativeWeight P.r s * ∑ k ∈ poleRange P n, d.coeff s k *
          ∑ l ∈ range (k-hh P n 1), (1 : ℚ)/((l : ℚ)+1)^(s+(P.r-1)))) = (a : ℚ) by
      obtain ⟨a, ha⟩ := hh
      exact ⟨-a, by rw [ha, Int.cast_neg]⟩
    apply zz_integer_sum
    intro s hs
    rw [mul_left_comm, mul_sum]
    apply zz_integer_mul (zz_weight_integer P.r s)
    apply zz_integer_sum
    intro k hk
    by_cases hk' : k ∈ orderPoleRange P n s
    · obtain ⟨a, ha⟩ := zz_integer_mul (hc s hs k hk)
        (zz_cleared_harmonic_integer P n s k hs hk')
      refine ⟨a, ?_⟩
      rw [← ha, zz_scale_factor P n s hs]
      ring
    · rw [zudilin_partial_fraction_pole_support P n hn d s hs k hk hk']
      exact ⟨0, by simp⟩
  · intro k hk
    have hk' := mem_Icc.mp hk
    have hs : 2*k+1 ∈ Icc 1 (P.q-P.r) := by apply mem_Icc.mpr; omega
    rw [PartialFractionData.zetaCoefficient, mul_left_comm, mul_sum]
    apply zz_integer_mul (zz_weight_integer P.r (2*k+1))
    apply zz_integer_sum
    intro j hj
    obtain ⟨a, ha⟩ := zz_integer_mul (⟨(prefixClearing P n (2*k+1) : ℤ), by simp⟩ :
      ∃ a : ℤ, (prefixClearing P n (2*k+1) : ℚ) = (a : ℚ)) (hc (2*k+1) hs j hj)
    refine ⟨a, ?_⟩
    rw [← ha, zz_scale_factor P n (2*k+1) hs]
    ring
