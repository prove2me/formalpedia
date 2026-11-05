-- Prove2me | solution 1 for StrongConv.abs_coeff_zero_le_and_sum_le_lpNormCircle
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T00:00:43.281894+00:00
-- url     : https://prove2.me/submissions/50c84e57-5b68-4d95-8bf5-671e97741522

import Definitions.Def_StrongConv
import Mathlib

section
section
open Finset Complex Polynomial

namespace StrongConvS4.L44



/-- `∑_{i=1}^M i^{γ-1} ≤ M^γ / γ`. -/
lemma sum_rpow_le (g : ℝ) (hg0 : 0 < g) (hg1 : g ≤ 1) (M : ℕ) :
    ∑ i ∈ Icc 1 M, ((i : ℕ) : ℝ) ^ (g - 1) ≤ (M : ℝ) ^ g / g := by
  induction M with
  | zero => simp [Real.zero_rpow hg0.ne']
  | succ M ih =>
    rw [sum_Icc_succ_top (by omega)]
    have key : ((M + 1 : ℕ) : ℝ) ^ (g - 1) ≤ (((M + 1 : ℕ) : ℝ) ^ g - (M : ℝ) ^ g) / g := by
      set x : ℝ := ((M + 1 : ℕ) : ℝ) with hx
      have hMx : (M : ℝ) = x - 1 := by rw [hx]; push_cast; ring
      have hx1 : 1 ≤ x := by rw [hx]; push_cast; linarith [(Nat.cast_nonneg M : (0:ℝ) ≤ M)]
      have hxp : 0 < x := by linarith
      have hb := rpow_one_add_le_one_add_mul_self (s := -1 / x) (by
        rw [le_div_iff₀ hxp]; linarith) hg0.le hg1
      have e1 : (M : ℝ) = x * (1 + -1 / x) := by rw [hMx]; field_simp; ring
      have e2 : (M : ℝ) ^ g = x ^ g * (1 + -1 / x) ^ g := by
        rw [e1]
        exact Real.mul_rpow hxp.le (by have : 1 / x ≤ 1 := (div_le_one hxp).2 hx1; rw [neg_div]; linarith)
      have e3 : x ^ (g - 1) = x ^ g / x := by
        rw [Real.rpow_sub hxp, Real.rpow_one]
      rw [e2, e3, le_div_iff₀ hg0]
      have : 0 ≤ x ^ g := by positivity
      have h4 : x ^ g * (1 + -1 / x) ^ g ≤ x ^ g * (1 + g * (-1 / x)) :=
        mul_le_mul_of_nonneg_left hb this
      have h5 : x ^ g / x * g = x ^ g * (g / x) := by ring
      nlinarith [h4, h5, show x ^ g * (1 + g * (-1 / x)) = x ^ g - x ^ g * (g / x) by ring]
    rw [sub_div] at key
    linarith [ih, key]


lemma conv_sum (s : ℕ) (hs : 1 ≤ s) (g d : ℝ) (hg0 : 0 < g) (hg1 : g ≤ 1) (hd0 : 0 < d) (hd1 : d ≤ 1) :
    ∑ j ∈ Ico 1 s, (((s - j : ℕ) : ℝ) ^ (g - 1)) * (1 / (j : ℝ))
      ≤ 2 * (s : ℝ) ^ (g + d - 1) * (1 / d + 1 / g) := by
  have hsp : (0:ℝ) < s := by exact_mod_cast hs
  have hs1 : (1:ℝ) ≤ s := by exact_mod_cast hs
  -- termwise
  have term : ∀ j ∈ Ico 1 s, (((s - j : ℕ) : ℝ) ^ (g - 1)) * (1 / (j : ℝ))
      ≤ 2 * (s : ℝ) ^ (g - 1) * (((j : ℕ) : ℝ) ^ (d - 1)) + (2 / (s : ℝ)) * (((s - j : ℕ) : ℝ) ^ (g - 1)) := by
    intro j hj
    rw [mem_Ico] at hj
    have hj1 : (1:ℝ) ≤ j := by exact_mod_cast hj.1
    have hjp : (0:ℝ) < j := by linarith
    have hsj : ((s - j : ℕ) : ℝ) = (s:ℝ) - j := by rw [Nat.cast_sub hj.2.le]
    have hsjp : (0:ℝ) < ((s - j : ℕ) : ℝ) := by
      have : 0 < s - j := by omega
      exact_mod_cast this
    have hjd : 1 / (j:ℝ) ≤ (j:ℝ) ^ (d - 1) := by
      rw [Real.rpow_sub hjp, Real.rpow_one]
      have : 1 ≤ (j:ℝ) ^ d := Real.one_le_rpow hj1 hd0.le
      gcongr
    have hA : 0 ≤ ((s - j : ℕ) : ℝ) ^ (g - 1) := by positivity
    have hB : 0 ≤ (s : ℝ) ^ (g - 1) := by positivity
    have hC : 0 ≤ (j : ℝ) ^ (d - 1) := by positivity
    by_cases hc : 2 * j ≤ s
    · have h1 : ((s - j : ℕ) : ℝ) ^ (g - 1) ≤ 2 * (s : ℝ) ^ (g - 1) := by
        have hh : (s:ℝ) / 2 ≤ ((s - j : ℕ) : ℝ) := by
          rw [hsj]; have : (2:ℝ) * j ≤ s := by exact_mod_cast hc
          linarith
        calc ((s - j : ℕ) : ℝ) ^ (g - 1) ≤ ((s:ℝ) / 2) ^ (g - 1) :=
              Real.rpow_le_rpow_of_nonpos (by positivity) hh (by linarith)
          _ = (s:ℝ) ^ (g - 1) * 2 ^ (1 - g) := by
              rw [Real.div_rpow hsp.le (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num)]
              congr 2; ring
          _ ≤ (s:ℝ) ^ (g - 1) * 2 := by
              gcongr
              calc (2:ℝ) ^ (1 - g) ≤ 2 ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
                _ = 2 := Real.rpow_one 2
          _ = 2 * (s : ℝ) ^ (g - 1) := by ring
      calc ((s - j : ℕ) : ℝ) ^ (g - 1) * (1 / (j:ℝ)) ≤ (2 * (s : ℝ) ^ (g - 1)) * (j:ℝ) ^ (d - 1) :=
            mul_le_mul h1 hjd (by positivity) (by positivity)
        _ ≤ _ := by
            have : 0 ≤ (2 / (s : ℝ)) * ((s - j : ℕ) : ℝ) ^ (g - 1) := by positivity
            linarith
    · push Not at hc
      have h2 : 1 / (j:ℝ) ≤ 2 / (s:ℝ) := by
        rw [div_le_div_iff₀ hjp hsp]
        have : (s:ℝ) < 2 * j := by exact_mod_cast hc
        linarith
      calc ((s - j : ℕ) : ℝ) ^ (g - 1) * (1 / (j:ℝ)) ≤ ((s - j : ℕ) : ℝ) ^ (g - 1) * (2 / (s:ℝ)) :=
            mul_le_mul_of_nonneg_left h2 hA
        _ ≤ _ := by
            have : 0 ≤ 2 * (s : ℝ) ^ (g - 1) * (j : ℝ) ^ (d - 1) := by positivity
            nlinarith
  refine (sum_le_sum term).trans ?_
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  have S1 : ∑ j ∈ Ico 1 s, ((j : ℕ) : ℝ) ^ (d - 1) ≤ (s:ℝ) ^ d / d := by
    refine le_trans ?_ (sum_rpow_le d hd0 hd1 s)
    apply sum_le_sum_of_subset_of_nonneg
    · intro j hj; rw [mem_Ico] at hj; rw [mem_Icc]; omega
    · intros; positivity
  have S2 : ∑ j ∈ Ico 1 s, (((s - j : ℕ) : ℝ) ^ (g - 1)) ≤ (s:ℝ) ^ g / g := by
    have : ∑ j ∈ Ico 1 s, (((s - j : ℕ) : ℝ) ^ (g - 1)) = ∑ i ∈ Ico 1 s, ((i : ℕ) : ℝ) ^ (g - 1) := by
      refine sum_nbij' (fun j => s - j) (fun i => s - i) ?_ ?_ ?_ ?_ ?_
      · intro j hj; rw [mem_Ico] at hj ⊢; omega
      · intro j hj; rw [mem_Ico] at hj ⊢; omega
      · intro j hj; rw [mem_Ico] at hj; omega
      · intro j hj; rw [mem_Ico] at hj; omega
      · intros; rfl
    rw [this]
    refine le_trans ?_ (sum_rpow_le g hg0 hg1 s)
    apply sum_le_sum_of_subset_of_nonneg
    · intro j hj; rw [mem_Ico] at hj; rw [mem_Icc]; omega
    · intros; positivity
  have hsg : (s:ℝ) ^ (g - 1) ≤ (s:ℝ) ^ (g + d - 1) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (by linarith)
  have e1 : (s:ℝ) ^ (g - 1) * (s:ℝ) ^ d = (s:ℝ) ^ (g + d - 1) := by
    rw [← Real.rpow_add hsp]; congr 1; ring
  have e2 : (2 / (s:ℝ)) * (s:ℝ) ^ g = 2 * (s:ℝ) ^ (g - 1) := by
    rw [Real.rpow_sub hsp, Real.rpow_one]; ring
  have t1 : 2 * (s:ℝ) ^ (g - 1) * ∑ j ∈ Ico 1 s, ((j : ℕ) : ℝ) ^ (d - 1)
      ≤ 2 * (s:ℝ) ^ (g + d - 1) * (1 / d) := by
    calc _ ≤ 2 * (s:ℝ) ^ (g - 1) * ((s:ℝ) ^ d / d) := by gcongr
      _ = 2 * ((s:ℝ) ^ (g - 1) * (s:ℝ) ^ d) * (1 / d) := by ring
      _ = _ := by rw [e1]
  have t2 : 2 / (s:ℝ) * ∑ j ∈ Ico 1 s, (((s - j : ℕ) : ℝ) ^ (g - 1))
      ≤ 2 * (s:ℝ) ^ (g + d - 1) * (1 / g) := by
    calc _ ≤ 2 / (s:ℝ) * ((s:ℝ) ^ g / g) := by gcongr
      _ = ((2 / (s:ℝ)) * (s:ℝ) ^ g) * (1 / g) := by ring
      _ = 2 * (s:ℝ) ^ (g - 1) * (1 / g) := by rw [e2]
      _ ≤ _ := by gcongr
  linarith


lemma coeff_pow_zero (P : ℂ[X]) (h0 : P.coeff 0 = 0) (k : ℕ) (hk : 1 ≤ k) : (P ^ k).coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero, h0]
  exact zero_pow (by omega)

lemma coeff_pow_bound (P : ℂ[X]) (h0 : P.coeff 0 = 0) (h1 : ∀ j : ℕ, 1 ≤ j → ‖P.coeff j‖ ≤ 1 / (j : ℝ))
    (d : ℝ) (hd0 : 0 < d) (k : ℕ) (hk : 1 ≤ k) (hkd : k * d ≤ 1) :
    ∀ s : ℕ, 1 ≤ s → ‖(P ^ k).coeff s‖ ≤ (4 / d) ^ (k - 1) * (s : ℝ) ^ (k * d - 1) := by
  induction k, hk using Nat.le_induction with
  | base =>
    intro s hs
    have hsp : (0:ℝ) < s := by exact_mod_cast hs
    have hs1 : (1:ℝ) ≤ s := by exact_mod_cast hs
    simp only [pow_one, Nat.sub_self, pow_zero, one_mul, Nat.cast_one, one_mul]
    refine (h1 s hs).trans ?_
    rw [Real.rpow_sub hsp, Real.rpow_one]
    have : 1 ≤ (s:ℝ) ^ d := Real.one_le_rpow hs1 hd0.le
    gcongr
  | succ k hk ih =>
    intro s hs
    have hkd' : (k:ℝ) * d ≤ 1 := by
      push_cast at hkd; nlinarith
    have hkpos : (0:ℝ) < k * d := by
      have : (0:ℝ) < k := by exact_mod_cast hk
      positivity
    have hd1 : d ≤ 1 := by
      have : (1:ℝ) ≤ k := by exact_mod_cast hk
      nlinarith
    have ih := ih hkd'
    have h0k := coeff_pow_zero P h0 k hk
    rw [pow_succ', coeff_mul]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun j i => P.coeff j * (P ^ k).coeff i) s]
    refine (norm_sum_le _ _).trans ?_
    simp only [norm_mul]
    have hsub : ∑ j ∈ Ico 1 s, ‖P.coeff j‖ * ‖(P ^ k).coeff (s - j)‖
        = ∑ j ∈ range (s.succ), ‖P.coeff j‖ * ‖(P ^ k).coeff (s - j)‖ := by
      apply sum_subset
      · intro j hj; rw [mem_Ico] at hj; rw [mem_range]; omega
      · intro j hj hj'
        rw [mem_range] at hj; rw [mem_Ico] at hj'
        by_cases hj0 : j = 0
        · subst hj0; simp [h0]
        · have : j = s := by omega
          subst this; simp [h0k]
    rw [← hsub]
    have hc : (0:ℝ) ≤ (4 / d) ^ (k - 1) := by positivity
    calc ∑ j ∈ Ico 1 s, ‖P.coeff j‖ * ‖(P ^ k).coeff (s - j)‖
        ≤ ∑ j ∈ Ico 1 s, (4 / d) ^ (k - 1) * ((((s - j : ℕ) : ℝ) ^ ((k:ℝ) * d - 1)) * (1 / (j : ℝ))) := by
          apply sum_le_sum
          intro j hj
          rw [mem_Ico] at hj
          have a1 := h1 j hj.1
          have a2 := ih (s - j) (by omega)
          calc ‖P.coeff j‖ * ‖(P ^ k).coeff (s - j)‖
              ≤ (1 / (j:ℝ)) * ((4 / d) ^ (k - 1) * (((s - j : ℕ) : ℝ) ^ ((k:ℝ) * d - 1))) :=
                mul_le_mul a1 a2 (norm_nonneg _) (by positivity)
            _ = _ := by ring
      _ = (4 / d) ^ (k - 1) * ∑ j ∈ Ico 1 s, (((s - j : ℕ) : ℝ) ^ ((k:ℝ) * d - 1)) * (1 / (j : ℝ)) := by
          rw [mul_sum]
      _ ≤ (4 / d) ^ (k - 1) * (2 * (s : ℝ) ^ ((k:ℝ) * d + d - 1) * (1 / d + 1 / ((k:ℝ) * d))) := by
          gcongr
          exact conv_sum s hs _ _ hkpos hkd' hd0 hd1
      _ ≤ (4 / d) ^ (k + 1 - 1) * (s : ℝ) ^ (((k + 1 : ℕ) : ℝ) * d - 1) := by
          have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
          have : 1 / d + 1 / ((k:ℝ) * d) ≤ 2 / d := by
            have : 1 / ((k:ℝ) * d) ≤ 1 / d := by
              apply one_div_le_one_div_of_le hd0; nlinarith
            have : 2 / d = 1 / d + 1 / d := by ring
            linarith
          have hsp : (0:ℝ) < (s:ℝ) ^ ((k:ℝ) * d + d - 1) := by
            have : (0:ℝ) < s := by exact_mod_cast hs
            positivity
          have e : (4 / d) ^ (k + 1 - 1) = (4 / d) ^ (k - 1) * (4 / d) := by
            rw [← pow_succ]; congr 1; omega
          have e2 : ((k + 1 : ℕ) : ℝ) * d - 1 = (k:ℝ) * d + d - 1 := by push_cast; ring
          rw [e, e2]
          have : 2 * (s : ℝ) ^ ((k:ℝ) * d + d - 1) * (1 / d + 1 / ((k:ℝ) * d))
              ≤ 2 * (s : ℝ) ^ ((k:ℝ) * d + d - 1) * (2 / d) := by gcongr
          calc (4 / d) ^ (k - 1) * (2 * (s : ℝ) ^ ((k:ℝ) * d + d - 1) * (1 / d + 1 / ((k:ℝ) * d)))
              ≤ (4 / d) ^ (k - 1) * (2 * (s : ℝ) ^ ((k:ℝ) * d + d - 1) * (2 / d)) := by gcongr
            _ = _ := by ring





lemma int_exp (m : ℤ) :
    ∫ θ in (0:ℝ)..2 * Real.pi, Complex.exp (((m:ℂ) * I) * (θ:ℂ))
      = if m = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0 := by
  by_cases hm : m = 0
  · subst hm; simp
  · rw [if_neg hm]
    have hc : ((m:ℂ) * I) ≠ 0 := mul_ne_zero (by exact_mod_cast hm) I_ne_zero
    rw [integral_exp_mul_complex hc]
    have : Complex.exp (((m:ℂ) * I) * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I m]; congr 1; push_cast; ring
    rw [this]; simp

lemma parseval (N : ℕ) (c : ℕ → ℂ) :
    ∫ θ in (0:ℝ)..2 * Real.pi, ‖∑ k ∈ range N, c k * Complex.exp (((k:ℕ):ℂ) * I * (θ:ℂ))‖ ^ 2
      = 2 * Real.pi * ∑ k ∈ range N, ‖c k‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have e : ∀ θ : ℝ, (((‖∑ k ∈ range N, c k * Complex.exp (((k:ℕ):ℂ) * I * (θ:ℂ))‖ ^ 2 : ℝ)) : ℂ)
      = ∑ k ∈ range N, ∑ l ∈ range N, (c k * (starRingEnd ℂ) (c l)) *
          Complex.exp ((((k:ℂ) - (l:ℂ)) * I * (θ:ℂ))) := by
    intro θ
    push_cast; rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
    rw [map_mul, ← Complex.exp_conj]
    have : (starRingEnd ℂ) (((l:ℕ):ℂ) * I * (θ:ℂ)) = -(((l:ℕ):ℂ) * I * (θ:ℂ)) := by
      simp [Complex.conj_ofReal]
    rw [this]
    have h2 : Complex.exp (((k:ℂ) - (l:ℂ)) * I * (θ:ℂ))
        = Complex.exp (((k:ℕ):ℂ) * I * (θ:ℂ)) * Complex.exp (-(((l:ℕ):ℂ) * I * (θ:ℂ))) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [h2]; ring
  simp_rw [e]
  have e2 : ∀ k l : ℕ, ∀ θ : ℝ, Complex.exp (((k:ℂ) - (l:ℂ)) * I * (θ:ℂ))
      = Complex.exp ((((k:ℤ) - (l:ℤ) : ℤ) : ℂ) * I * (θ:ℂ)) := by
    intro k l θ; congr 1; push_cast; ring
  simp_rw [e2]
  have hc : ∀ k l : ℕ, Continuous (fun θ : ℝ => c k * (starRingEnd ℂ) (c l) *
      Complex.exp ((((k:ℤ) - (l:ℤ) : ℤ) : ℂ) * I * (θ:ℂ))) := fun k l => by fun_prop
  rw [intervalIntegral.integral_finsetSum]
  · have : ∀ k ∈ range N, ∫ θ in (0:ℝ)..2 * Real.pi, ∑ l ∈ range N, c k * (starRingEnd ℂ) (c l) *
        Complex.exp ((((k:ℤ) - (l:ℤ) : ℤ) : ℂ) * I * (θ:ℂ))
        = ((2 * Real.pi : ℝ) : ℂ) * ((‖c k‖ ^ 2 : ℝ) : ℂ) := by
      intro k hk
      rw [intervalIntegral.integral_finsetSum (fun l _ => (hc k l).intervalIntegrable _ _)]
      have : ∀ l ∈ range N, ∫ θ in (0:ℝ)..2 * Real.pi, c k * (starRingEnd ℂ) (c l) *
          Complex.exp ((((k:ℤ) - (l:ℤ) : ℤ) : ℂ) * I * (θ:ℂ))
          = if l = k then ((2 * Real.pi : ℝ) : ℂ) * (c k * (starRingEnd ℂ) (c k)) else 0 := by
        intro l _
        rw [intervalIntegral.integral_const_mul, int_exp]
        by_cases h : l = k
        · subst h; simp; ring
        · have : ((k:ℤ) - (l:ℤ)) ≠ 0 := by omega
          simp [this, h]
      rw [sum_congr rfl this, sum_ite_eq' (range N) k]
      rw [if_pos hk, Complex.mul_conj']; push_cast; ring
    rw [sum_congr rfl this]
    push_cast
    rw [← mul_sum]
  · intro k _
    exact (continuous_finset_sum _ fun l _ => hc k l).intervalIntegrable _ _





/-- `G_q(θ) = ∑_{j=1}^q ε_j cos(jθ+φ)/j`. -/
noncomputable def Gfun (q : ℕ) (ε : ℕ → ℝ) (φ θ : ℝ) : ℝ :=
  ∑ j ∈ Icc 1 q, ε j / j * Real.cos (j * θ + φ)

noncomputable def Ppoly (q : ℕ) (ε : ℕ → ℝ) : ℂ[X] :=
  ∑ j ∈ Icc 1 q, C (((ε j / j : ℝ)) : ℂ) * X ^ j

lemma Ppoly_coeff (q : ℕ) (ε : ℕ → ℝ) (j : ℕ) :
    (Ppoly q ε).coeff j = if j ∈ Icc 1 q then (((ε j / j : ℝ)) : ℂ) else 0 := by
  unfold Ppoly
  rw [finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  rw [sum_ite_eq (Icc 1 q) j]

lemma Ppoly_coeff_zero (q : ℕ) (ε : ℕ → ℝ) : (Ppoly q ε).coeff 0 = 0 := by
  rw [Ppoly_coeff]; simp

lemma Ppoly_coeff_norm (q : ℕ) (ε : ℕ → ℝ) (hε : ∀ j, |ε j| ≤ 1) (j : ℕ) (hj : 1 ≤ j) :
    ‖(Ppoly q ε).coeff j‖ ≤ 1 / (j : ℝ) := by
  rw [Ppoly_coeff]
  have hjp : (0:ℝ) < j := by exact_mod_cast hj
  split_ifs
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hjp]
    gcongr
    exact hε j
  · simp

lemma Ppoly_eval (q : ℕ) (ε : ℕ → ℝ) (θ : ℝ) :
    (Ppoly q ε).eval (Complex.exp ((θ:ℂ) * I)) =
      ∑ j ∈ Icc 1 q, (((ε j / j : ℝ)) : ℂ) * Complex.exp (((j * θ : ℝ) : ℂ) * I) := by
  unfold Ppoly
  rw [eval_finsetSum]
  refine sum_congr rfl fun j _ => ?_
  rw [eval_mul, eval_C, eval_pow, eval_X, ← Complex.exp_nat_mul]
  congr 2
  push_cast; ring

lemma Gfun_le (q : ℕ) (ε : ℕ → ℝ) (φ θ : ℝ) :
    |Gfun q ε φ θ| ≤ ‖(Ppoly q ε).eval (Complex.exp ((θ:ℂ) * I))‖ := by
  rw [Ppoly_eval]
  have : Gfun q ε φ θ = (Complex.exp ((φ:ℂ) * I) *
      ∑ j ∈ Icc 1 q, (((ε j / j : ℝ)) : ℂ) * Complex.exp (((j * θ : ℝ) : ℂ) * I)).re := by
    rw [mul_sum, Complex.re_sum]
    unfold Gfun
    refine sum_congr rfl fun j _ => ?_
    have : Complex.exp ((φ:ℂ) * I) * ((((ε j / j : ℝ)) : ℂ) * Complex.exp (((j * θ : ℝ) : ℂ) * I))
        = (((ε j / j : ℝ)) : ℂ) * Complex.exp (((j * θ + φ : ℝ) : ℂ) * I) := by
      rw [show (((j * θ + φ : ℝ) : ℂ) * I) = ((j * θ : ℝ) : ℂ) * I + (φ:ℂ) * I by push_cast; ring,
        Complex.exp_add]; ring
    rw [this, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  rw [this]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]





lemma sum_inv32_aux (N : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ Icc 1 N, 1 / ((k:ℝ) * Real.sqrt k) ≤ 3 - 2 / Real.sqrt N := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ N hN ih =>
    rw [sum_Icc_succ_top (by omega)]
    have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
    set a := Real.sqrt N with ha
    set b := Real.sqrt ((N + 1 : ℕ) : ℝ) with hb
    have ha0 : 0 < a := Real.sqrt_pos.2 (by linarith)
    have hb0' : 0 < b := Real.sqrt_pos.2 (by push_cast; linarith)
    have ha2 : a ^ 2 = N := Real.sq_sqrt (by linarith)
    have hb2 : b ^ 2 = N + 1 := by rw [hb]; push_cast; exact Real.sq_sqrt (by linarith)
    have hab : a < b := by
      by_contra h; push Not at h; nlinarith [mul_self_le_mul_self hb0'.le h]
    have hb0 : 0 < b := hb0'
    have : 1 / (((N + 1 : ℕ) : ℝ) * b) ≤ 2 / a - 2 / b := by
      have e : ((N + 1 : ℕ) : ℝ) = b ^ 2 := by push_cast; linarith
      rw [e, div_sub_div _ _ ha0.ne' hb0.ne', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos ha0 hb0, mul_pos (mul_pos ha0 hb0) hb0, mul_pos (mul_pos ha0 hb0) (mul_pos hb0 hb0)]
    linarith

lemma sum_inv32 (N : ℕ) : ∑ k ∈ Icc 1 N, ((k:ℝ) ^ (-(3/4) : ℝ)) ^ 2 ≤ 3 := by
  have e : ∀ k ∈ Icc 1 N, ((k:ℝ) ^ (-(3/4) : ℝ)) ^ 2 = 1 / ((k:ℝ) * Real.sqrt k) := by
    intro k hk
    have hk1 : (1:ℝ) ≤ k := by rw [mem_Icc] at hk; exact_mod_cast hk.1
    have hkp : (0:ℝ) < k := by linarith
    have h1 : (k:ℝ) * Real.sqrt k = (k:ℝ) ^ ((3:ℝ)/2) := by
      calc (k:ℝ) * Real.sqrt k = (k:ℝ) ^ (1:ℝ) * (k:ℝ) ^ ((1:ℝ)/2) := by
            rw [Real.rpow_one, Real.sqrt_eq_rpow]
        _ = (k:ℝ) ^ ((1:ℝ) + 1/2) := (Real.rpow_add hkp _ _).symm
        _ = _ := by norm_num
    rw [h1, one_div, ← Real.rpow_neg hkp.le, ← Real.rpow_natCast, ← Real.rpow_mul hkp.le]
    congr 1; norm_num
  rw [sum_congr rfl e]
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp
  · have := sum_inv32_aux N h
    have : 0 ≤ 2 / Real.sqrt N := by positivity
    linarith


lemma moment (n : ℕ) (hn : 1 ≤ n) (q : ℕ) (ε : ℕ → ℝ) (hε : ∀ j, |ε j| ≤ 1) (φ : ℝ) :
    ∫ θ in (0:ℝ)..2 * Real.pi, (Gfun q ε φ θ) ^ (2 * n)
      ≤ 2 * Real.pi * (3 * ((16 * (n:ℝ)) ^ (n - 1)) ^ 2) := by
  set P := Ppoly q ε with hP
  have hnp : (0:ℝ) < n := by exact_mod_cast hn
  set d : ℝ := 1 / (4 * n) with hd
  have hd0 : 0 < d := by positivity
  have hnd : (n:ℝ) * d = 1 / 4 := by rw [hd]; field_simp
  have hbound := coeff_pow_bound P (Ppoly_coeff_zero q ε) (Ppoly_coeff_norm q ε hε) d hd0 n hn
    (by rw [hnd]; norm_num)
  have h4d : 4 / d = 16 * (n:ℝ) := by rw [hd]; field_simp; ring
  rw [h4d, hnd] at hbound
  have hc0 := coeff_pow_zero P (Ppoly_coeff_zero q ε) n hn
  -- pointwise
  have pt : ∀ θ : ℝ, (Gfun q ε φ θ) ^ (2 * n) ≤
      ‖∑ k ∈ range ((P ^ n).natDegree + 1), (P ^ n).coeff k * Complex.exp (((k:ℕ):ℂ) * I * (θ:ℂ))‖ ^ 2 := by
    intro θ
    have h1 : ∑ k ∈ range ((P ^ n).natDegree + 1), (P ^ n).coeff k * Complex.exp (((k:ℕ):ℂ) * I * (θ:ℂ))
        = (P.eval (Complex.exp ((θ:ℂ) * I))) ^ n := by
      rw [← eval_pow, eval_eq_sum_range]
      refine sum_congr rfl fun k _ => ?_
      rw [← Complex.exp_nat_mul]; congr 2; ring
    rw [h1, norm_pow, ← pow_mul, mul_comm n 2]
    calc (Gfun q ε φ θ) ^ (2 * n) = |Gfun q ε φ θ| ^ (2 * n) := (Even.pow_abs ⟨n, by ring⟩ _).symm
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) (Gfun_le q ε φ θ) _
  have hcont : Continuous (fun θ : ℝ => (Gfun q ε φ θ) ^ (2 * n)) := by
    unfold Gfun; fun_prop
  have hcont2 : Continuous (fun θ : ℝ =>
      ‖∑ k ∈ range ((P ^ n).natDegree + 1), (P ^ n).coeff k * Complex.exp (((k:ℕ):ℂ) * I * (θ:ℂ))‖ ^ 2) := by
    fun_prop
  calc ∫ θ in (0:ℝ)..2 * Real.pi, (Gfun q ε φ θ) ^ (2 * n)
      ≤ ∫ θ in (0:ℝ)..2 * Real.pi,
        ‖∑ k ∈ range ((P ^ n).natDegree + 1), (P ^ n).coeff k * Complex.exp (((k:ℕ):ℂ) * I * (θ:ℂ))‖ ^ 2 :=
        intervalIntegral.integral_mono_on (by positivity) (hcont.intervalIntegrable _ _)
          (hcont2.intervalIntegrable _ _) (fun θ _ => pt θ)
    _ = 2 * Real.pi * ∑ k ∈ range ((P ^ n).natDegree + 1), ‖(P ^ n).coeff k‖ ^ 2 := parseval _ _
    _ ≤ _ := by
      gcongr
      have : ∑ k ∈ range ((P ^ n).natDegree + 1), ‖(P ^ n).coeff k‖ ^ 2
          ≤ ∑ k ∈ range ((P ^ n).natDegree + 1), if k = 0 then 0 else
              ((16 * (n:ℝ)) ^ (n - 1)) ^ 2 * ((k:ℝ) ^ (-(3/4) : ℝ)) ^ 2 := by
        apply sum_le_sum
        intro k _
        by_cases hk : k = 0
        · subst hk; simp [hc0]
        · rw [if_neg hk]
          have := hbound k (by omega)
          have e : ((k:ℝ) ^ ((1:ℝ)/4 - 1)) = (k:ℝ) ^ (-(3/4) : ℝ) := by congr 1; norm_num
          rw [e] at this
          rw [← mul_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) this 2
      refine this.trans ?_
      rw [sum_range_succ']
      simp only [Nat.succ_ne_zero, if_false, if_true]
      have : ∀ N : ℕ, ∑ i ∈ range N, ((16 * (n:ℝ)) ^ (n - 1)) ^ 2 * (((i + 1 : ℕ) : ℝ) ^ (-(3/4) : ℝ)) ^ 2
          = ((16 * (n:ℝ)) ^ (n - 1)) ^ 2 * ∑ k ∈ Icc 1 N, ((k:ℝ) ^ (-(3/4) : ℝ)) ^ 2 := by
        intro N
        rw [mul_sum]
        induction N with
        | zero => simp
        | succ N ih => rw [sum_range_succ, sum_Icc_succ_top (by omega), ih]
      rw [this]
      nlinarith [sum_inv32 ((P ^ n).natDegree), sq_nonneg ((16 * (n:ℝ)) ^ (n - 1))]

open MeasureTheory in
lemma lpnorm_toReal {f : ℝ → ℝ} {μ : Measure ℝ} (r : ℝ) (hr : 0 < r)
    (hf : MemLp f (ENNReal.ofReal r) μ) :
    (eLpNorm f (ENNReal.ofReal r) μ).toReal = (∫ a, ‖f a‖ ^ r ∂μ) ^ r⁻¹ := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by simpa using hr) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal hr.le]

lemma Gfun_continuous (q : ℕ) (ε : ℕ → ℝ) (φ : ℝ) : Continuous (Gfun q ε φ) := by
  unfold Gfun; fun_prop

lemma Gfun_bound (q : ℕ) (ε : ℕ → ℝ) (hε : ∀ j, |ε j| ≤ 1) (φ θ : ℝ) : |Gfun q ε φ θ| ≤ q := by
  unfold Gfun
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j ∈ Icc 1 q, |ε j / j * Real.cos (j * θ + φ)| ≤ ∑ j ∈ Icc 1 q, (1:ℝ) := by
        apply sum_le_sum
        intro j hj
        rw [mem_Icc] at hj
        have hjp : (1:ℝ) ≤ j := by exact_mod_cast hj.1
        rw [abs_mul, abs_div, Nat.abs_cast]
        calc |ε j| / j * |Real.cos (j * θ + φ)| ≤ 1 / j * 1 := by
              gcongr
              · exact hε j
              · exact Real.abs_cos_le_one _
          _ ≤ 1 := by rw [mul_one]; exact (div_le_one (by linarith)).2 hjp
    _ = q := by simp

open MeasureTheory in
lemma G_lp_bound : ∃ C0 : ℝ, ∀ (q : ℕ) (ε : ℕ → ℝ), (∀ j, |ε j| ≤ 1) → ∀ φ : ℝ, ∀ p : ℝ, 1 ≤ p →
    (eLpNorm (Gfun q ε φ) (ENNReal.ofReal p) (volume.restrict (Set.Icc 0 (2 * Real.pi)))).toReal ≤ C0 * p := by
  refine ⟨3200, fun q ε hε φ p hp => ?_⟩
  set μ : Measure ℝ := volume.restrict (Set.Icc 0 (2 * Real.pi)) with hμ
  have : IsFiniteMeasure μ := ⟨by rw [hμ, Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  have hGc := Gfun_continuous q ε φ
  have hmem : ∀ r : ENNReal, MemLp (Gfun q ε φ) r μ := fun r =>
    MemLp.of_bound hGc.aestronglyMeasurable q (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact Gfun_bound q ε hε φ x)
  set n : ℕ := ⌈p / 2⌉₊ with hn
  have hn1 : 1 ≤ n := by
    rw [hn]; exact Nat.one_le_iff_ne_zero.2 (by
      intro h; have := Nat.ceil_eq_zero.1 h; linarith)
  have hn2 : p ≤ 2 * n := by
    have := Nat.le_ceil (p / 2); rw [← hn] at this; linarith
  have hn3 : (n:ℝ) < p / 2 + 1 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ p / 2 by linarith); rw [← hn] at this; exact this
  have hnp : (1:ℝ) ≤ n := by exact_mod_cast hn1
  have hpos : (0:ℝ) < p := by linarith
  have h2n : (0:ℝ) < 2 * n := by linarith
  -- the 2n norm
  have hnorm2n : (eLpNorm (Gfun q ε φ) (ENNReal.ofReal (2 * n)) μ).toReal ≤ 304 * n := by
    rw [lpnorm_toReal _ h2n (hmem _)]
    have hint : ∫ a, ‖Gfun q ε φ a‖ ^ (2 * (n:ℝ)) ∂μ ≤ (304 * (n:ℝ)) ^ (2 * n) := by
      have e1 : ∀ a, ‖Gfun q ε φ a‖ ^ (2 * (n:ℝ)) = (Gfun q ε φ a) ^ (2 * n) := by
        intro a
        rw [Real.norm_eq_abs, show (2 * (n:ℝ)) = ((2 * n : ℕ) : ℝ) by push_cast; ring,
          Real.rpow_natCast]
        exact Even.pow_abs ⟨n, by ring⟩ _
      simp_rw [e1]
      rw [hμ, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by positivity)]
      refine (moment n hn1 q ε hε φ).trans ?_
      have hA : (16 * (n:ℝ)) ^ (n - 1) ≥ 0 := by positivity
      -- 2π * 3 * ((16 n)^(n-1))^2 ≤ (304 n)^(2n)
      have h16 : ((16 * (n:ℝ)) ^ (n - 1)) ^ 2 ≤ (16 * (n:ℝ)) ^ (2 * n) := by
        rw [← pow_mul]
        apply pow_le_pow_right₀ (by linarith) (by omega)
      have h19 : 2 * Real.pi * 3 ≤ (19:ℝ) ^ (2 * n) := by
        have : (19:ℝ) ≤ 19 ^ (2 * n) := by
          calc (19:ℝ) = 19 ^ 1 := by norm_num
            _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
        nlinarith [Real.pi_lt_d2]
      calc 2 * Real.pi * (3 * ((16 * (n:ℝ)) ^ (n - 1)) ^ 2)
          = (2 * Real.pi * 3) * ((16 * (n:ℝ)) ^ (n - 1)) ^ 2 := by ring
        _ ≤ (19:ℝ) ^ (2 * n) * (16 * (n:ℝ)) ^ (2 * n) := by
            apply mul_le_mul h19 h16 (by positivity) (by positivity)
        _ = (304 * (n:ℝ)) ^ (2 * n) := by rw [← mul_pow]; ring
    have hnn : 0 ≤ ∫ a, ‖Gfun q ε φ a‖ ^ (2 * (n:ℝ)) ∂μ := integral_nonneg fun a => by positivity
    calc (∫ a, ‖Gfun q ε φ a‖ ^ (2 * (n:ℝ)) ∂μ) ^ (2 * (n:ℝ))⁻¹
        ≤ ((304 * (n:ℝ)) ^ (2 * n)) ^ (2 * (n:ℝ))⁻¹ :=
          Real.rpow_le_rpow hnn hint (by positivity)
      _ = 304 * n := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
          push_cast
          rw [mul_inv_cancel₀ h2n.ne', Real.rpow_one]
  -- compare p and 2n
  have hcmp : eLpNorm (Gfun q ε φ) (ENNReal.ofReal p) μ ≤
      eLpNorm (Gfun q ε φ) (ENNReal.ofReal (2 * n)) μ * μ Set.univ ^ (1 / p - 1 / (2 * (n:ℝ))) := by
    have := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ) (f := Gfun q ε φ)
      (p := ENNReal.ofReal p) (q := ENNReal.ofReal (2 * n))
      (ENNReal.ofReal_le_ofReal hn2) hGc.aestronglyMeasurable
    rwa [ENNReal.toReal_ofReal hpos.le, ENNReal.toReal_ofReal h2n.le] at this
  have hμu : μ Set.univ = ENNReal.ofReal (2 * Real.pi) := by
    rw [hμ, Measure.restrict_apply_univ]; simp
  have hexp : 0 ≤ 1 / p - 1 / (2 * (n:ℝ)) := by
    rw [sub_nonneg]; exact one_div_le_one_div_of_le hpos hn2
  have hfin : eLpNorm (Gfun q ε φ) (ENNReal.ofReal (2 * n)) μ ≠ ⊤ := (hmem _).2.ne
  have h3 := ENNReal.toReal_mono (by
    refine ENNReal.mul_ne_top hfin ?_
    rw [hμu]; exact ENNReal.rpow_ne_top_of_nonneg hexp ENNReal.ofReal_ne_top) hcmp
  rw [ENNReal.toReal_mul, hμu, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (by positivity)] at h3
  have hpi : (1:ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have h4 : (2 * Real.pi) ^ (1 / p - 1 / (2 * (n:ℝ))) ≤ 7 := by
    calc (2 * Real.pi) ^ (1 / p - 1 / (2 * (n:ℝ))) ≤ (2 * Real.pi) ^ (1:ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le hpi
          have : 1 / p ≤ 1 := (div_le_one hpos).2 hp
          have : 0 < 1 / (2 * (n:ℝ)) := by positivity
          linarith
      _ ≤ 7 := by rw [Real.rpow_one]; linarith [Real.pi_lt_d2]
  calc _ ≤ _ := h3
    _ ≤ (304 * (n:ℝ)) * 7 := by
        apply mul_le_mul hnorm2n h4 (by positivity) (by positivity)
    _ ≤ 3200 * p := by nlinarith

lemma int_cos_phase (c : ℤ) (d : ℝ) :
    ∫ θ in (0:ℝ)..2 * Real.pi, Real.cos ((c:ℝ) * θ + d)
      = if c = 0 then 2 * Real.pi * Real.cos d else 0 := by
  by_cases hc : c = 0
  · subst hc; simp
  · have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
    rw [if_neg hc, intervalIntegral.integral_comp_mul_add (fun x => Real.cos x) hc']
    simp only [integral_cos, smul_eq_mul]
    have : Real.sin ((c:ℝ) * (2 * Real.pi) + d) = Real.sin ((c:ℝ) * 0 + d) := by
      rw [mul_zero, zero_add, show (c:ℝ) * (2 * Real.pi) + d = d + c * (2 * Real.pi) by ring,
        Real.sin_add_int_mul_two_pi]
    rw [this]; simp

lemma orth_phase (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (φ : ℝ) :
    ∫ θ in (0:ℝ)..2 * Real.pi, Real.cos (i * θ + φ) * Real.cos (j * θ + φ)
      = if i = j then Real.pi else 0 := by
  have e : ∀ θ : ℝ, Real.cos (i * θ + φ) * Real.cos (j * θ + φ)
      = (1/2) * (Real.cos ((((i:ℤ) - j : ℤ) : ℝ) * θ + 0) + Real.cos ((((i:ℤ) + j : ℤ) : ℝ) * θ + 2 * φ)) := by
    intro θ
    push_cast
    have h1 : Real.cos (i * θ + φ) * Real.cos (j * θ + φ)
        = (Real.cos ((i * θ + φ) - (j * θ + φ)) + Real.cos ((i * θ + φ) + (j * θ + φ))) / 2 := by
      rw [Real.cos_sub (i * θ + φ) (j * θ + φ), Real.cos_add (i * θ + φ) (j * θ + φ)]; ring
    rw [h1]
    have a1 : (i * θ + φ) - (j * θ + φ) = ((i:ℝ) - j) * θ + 0 := by ring
    have a2 : (i * θ + φ) + (j * θ + φ) = ((i:ℝ) + j) * θ + 2 * φ := by ring
    rw [a1, a2]; ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _),
    int_cos_phase, int_cos_phase]
  by_cases hij : i = j
  · subst hij
    simp
    have : i ≠ 0 := by omega
    simp [this]
  · have h1 : (i:ℤ) - j ≠ 0 := by omega
    have h2 : (i:ℤ) + j ≠ 0 := by omega
    simp [h1, h2, hij]

lemma iter_F (q : ℕ) (a : ℕ → ℝ) (n : ℕ) :
    iteratedDeriv n (fun θ : ℝ => ∑ j ∈ range (q + 1), a j * Real.cos (j * θ))
      = fun θ => ∑ j ∈ range (q + 1), a j * (j:ℝ) ^ n * Real.cos (j * θ + n * (Real.pi / 2)) := by
  induction n with
  | zero => funext θ; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext θ
    apply HasDerivAt.deriv
    have : ∀ j ∈ range (q + 1), HasDerivAt (fun θ : ℝ => a j * (j:ℝ) ^ n * Real.cos (j * θ + n * (Real.pi / 2)))
        (a j * (j:ℝ) ^ (n + 1) * Real.cos (j * θ + ((n + 1 : ℕ) : ℝ) * (Real.pi / 2))) θ := by
      intro j _
      have h1 : HasDerivAt (fun θ : ℝ => (j:ℝ) * θ + n * (Real.pi / 2)) (j:ℝ) θ := by
        simpa using ((hasDerivAt_id θ).const_mul (j:ℝ)).add_const ((n:ℝ) * (Real.pi / 2))
      have h2 := (h1.cos).const_mul (a j * (j:ℝ) ^ n)
      refine h2.congr_deriv ?_
      have : Real.cos (j * θ + ((n + 1 : ℕ) : ℝ) * (Real.pi / 2))
          = -Real.sin (j * θ + n * (Real.pi / 2)) := by
        rw [show (j:ℝ) * θ + ((n + 1 : ℕ) : ℝ) * (Real.pi / 2) = (j * θ + n * (Real.pi / 2)) + Real.pi / 2 by
          push_cast; ring, Real.cos_add_pi_div_two]
      rw [this]; ring
    exact HasDerivAt.fun_sum this

noncomputable def epsS (a : ℕ → ℝ) (j : ℕ) : ℝ := if 0 ≤ a j then 1 else -1

lemma epsS_abs (a : ℕ → ℝ) (j : ℕ) : |epsS a j| ≤ 1 := by
  unfold epsS; split_ifs <;> simp

lemma epsS_mul (a : ℕ → ℝ) (j : ℕ) : a j * epsS a j = |a j| := by
  unfold epsS; split_ifs with h
  · rw [mul_one, abs_of_nonneg h]
  · push Not at h; rw [mul_neg_one, abs_of_neg h]

lemma key_integral (q : ℕ) (a : ℕ → ℝ) (m : ℕ) (φ : ℝ) :
    ∫ θ in (0:ℝ)..2 * Real.pi,
      (∑ i ∈ Icc 1 q, a i * (i:ℝ) ^ (m + 1) * Real.cos (i * θ + φ)) * Gfun q (epsS a) φ θ
      = Real.pi * ∑ j ∈ Icc 1 q, (j:ℝ) ^ m * |a j| := by
  unfold Gfun
  simp_rw [sum_mul_sum]
  have hc : ∀ i j : ℕ, Continuous (fun θ : ℝ => a i * (i:ℝ) ^ (m + 1) * Real.cos (i * θ + φ) *
      (epsS a j / j * Real.cos (j * θ + φ))) := fun i j => by fun_prop
  rw [intervalIntegral.integral_finsetSum]
  · have : ∀ i ∈ Icc 1 q, ∫ θ in (0:ℝ)..2 * Real.pi, ∑ j ∈ Icc 1 q,
        a i * (i:ℝ) ^ (m + 1) * Real.cos (i * θ + φ) * (epsS a j / j * Real.cos (j * θ + φ))
        = Real.pi * ((i:ℝ) ^ m * |a i|) := by
      intro i hi
      rw [mem_Icc] at hi
      rw [intervalIntegral.integral_finsetSum (fun j _ => (hc i j).intervalIntegrable _ _)]
      have : ∀ j ∈ Icc 1 q, ∫ θ in (0:ℝ)..2 * Real.pi,
          a i * (i:ℝ) ^ (m + 1) * Real.cos (i * θ + φ) * (epsS a j / j * Real.cos (j * θ + φ))
          = if j = i then (a i * (i:ℝ) ^ (m + 1) * (epsS a j / j)) * Real.pi else 0 := by
        intro j hj
        rw [mem_Icc] at hj
        have e : ∀ θ : ℝ, a i * (i:ℝ) ^ (m + 1) * Real.cos (i * θ + φ) * (epsS a j / j * Real.cos (j * θ + φ))
            = (a i * (i:ℝ) ^ (m + 1) * (epsS a j / j)) * (Real.cos (i * θ + φ) * Real.cos (j * θ + φ)) := by
          intro θ; ring
        simp_rw [e]
        rw [intervalIntegral.integral_const_mul, orth_phase i j hi.1 hj.1]
        by_cases h : j = i
        · subst h; simp
        · have : ¬ i = j := fun h' => h h'.symm
          simp [h, this]
      rw [sum_congr rfl this, sum_ite_eq' (Icc 1 q) i, if_pos (mem_Icc.2 hi)]
      have hip : (0:ℝ) < i := by exact_mod_cast hi.1
      have : a i * (i:ℝ) ^ (m + 1) * (epsS a i / i) = (i:ℝ) ^ m * |a i| := by
        rw [← epsS_mul a i, pow_succ]; field_simp
      rw [this]; ring
    rw [sum_congr rfl this, ← mul_sum]
  · intro i _
    exact (continuous_finset_sum _ fun j _ => hc i j).intervalIntegrable _ _

lemma sum_range_to_Icc (q : ℕ) (f : ℕ → ℝ) (h0 : f 0 = 0) :
    ∑ i ∈ range (q + 1), f i = ∑ i ∈ Icc 1 q, f i := by
  symm
  apply sum_subset
  · intro i hi; rw [mem_Icc] at hi; rw [mem_range]; omega
  · intro i hi hi'
    rw [mem_range] at hi; rw [mem_Icc] at hi'
    have : i = 0 := by omega
    subst this; exact h0

open MeasureTheory in
lemma partii_core (C0 : ℝ)
    (hC0 : ∀ (q : ℕ) (ε : ℕ → ℝ), (∀ j, |ε j| ≤ 1) → ∀ φ : ℝ, ∀ p : ℝ, 1 ≤ p →
      (eLpNorm (Gfun q ε φ) (ENNReal.ofReal p) (volume.restrict (Set.Icc 0 (2 * Real.pi)))).toReal ≤ C0 * p)
    (q : ℕ) (a : ℕ → ℝ) (m : ℕ) (β : ℝ) (hβ : 1 < β) :
    ∑ j ∈ Icc 1 q, (j:ℝ) ^ m * |a j| ≤ C0 / Real.pi * (1 - 1 / β)⁻¹ *
      (eLpNorm (fun θ : ℝ => ∑ j ∈ range (q + 1), a j * (j:ℝ) ^ (m + 1) *
          Real.cos (j * θ + ((m + 1 : ℕ) : ℝ) * (Real.pi / 2)))
        (ENNReal.ofReal β) (volume.restrict (Set.Icc 0 (2 * Real.pi)))).toReal := by
  set φ : ℝ := ((m + 1 : ℕ) : ℝ) * (Real.pi / 2) with hφ
  set D : ℝ → ℝ := fun θ : ℝ => ∑ j ∈ range (q + 1), a j * (j:ℝ) ^ (m + 1) *
          Real.cos (j * θ + φ) with hD
  set μ : Measure ℝ := volume.restrict (Set.Icc 0 (2 * Real.pi)) with hμ
  have : IsFiniteMeasure μ := ⟨by rw [hμ, Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  set G : ℝ → ℝ := Gfun q (epsS a) φ with hG
  have hDc : Continuous D := by rw [hD]; fun_prop
  have hGc : Continuous G := Gfun_continuous q (epsS a) φ
  have hDI : D = fun θ => ∑ i ∈ Icc 1 q, a i * (i:ℝ) ^ (m + 1) * Real.cos (i * θ + φ) := by
    funext θ
    exact sum_range_to_Icc q (fun i => a i * (i:ℝ) ^ (m + 1) * Real.cos (i * θ + φ)) (by simp)
  set p : ℝ := (1 - 1 / β)⁻¹ with hp
  have hβ0 : 0 < β := by linarith
  have hinv : 1 / β < 1 := by rw [div_lt_one hβ0]; exact hβ
  have hinv0 : 0 < 1 / β := by positivity
  have hpos : 0 < 1 - 1 / β := by linarith
  have hconj : β.HolderConjugate p := by
    rw [Real.holderConjugate_iff]
    refine ⟨hβ, ?_⟩
    rw [hp, inv_inv, one_div]; ring
  have hp1 : 1 ≤ p := by
    rw [hp]; apply one_le_inv₀ hpos |>.2; linarith
  have hp0 : 0 < p := by linarith
  have hDmem : MemLp D (ENNReal.ofReal β) μ := by
    refine MemLp.of_bound hDc.aestronglyMeasurable (∑ j ∈ range (q + 1), |a j * (j:ℝ) ^ (m + 1)|)
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, hD]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    calc |a j * (j:ℝ) ^ (m + 1)| * |Real.cos (j * x + φ)| ≤ |a j * (j:ℝ) ^ (m + 1)| * 1 := by
          gcongr; exact Real.abs_cos_le_one _
      _ = _ := mul_one _
  have hGmem : MemLp G (ENNReal.ofReal p) μ :=
    MemLp.of_bound hGc.aestronglyMeasurable q (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact Gfun_bound q (epsS a) (epsS_abs a) φ x)
  have hkey : ∫ θ in (0:ℝ)..2 * Real.pi, D θ * G θ = Real.pi * ∑ j ∈ Icc 1 q, (j:ℝ) ^ m * |a j| := by
    rw [hDI]; exact key_integral q a m φ
  have hle : (0:ℝ) ≤ 2 * Real.pi := by positivity
  have hint : ∫ θ in (0:ℝ)..2 * Real.pi, D θ * G θ = ∫ θ, D θ * G θ ∂μ := by
    rw [intervalIntegral.integral_of_le hle, hμ, integral_Icc_eq_integral_Ioc]
  have h1 : ∫ θ, D θ * G θ ∂μ ≤ ∫ θ, ‖D θ‖ * ‖G θ‖ ∂μ := by
    calc ∫ θ, D θ * G θ ∂μ ≤ ‖∫ θ, D θ * G θ ∂μ‖ := le_abs_self _
      _ ≤ ∫ θ, ‖D θ * G θ‖ ∂μ := norm_integral_le_integral_norm _
      _ = _ := by simp_rw [norm_mul]
  have h2 := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hconj
    (f := fun θ => ‖D θ‖) (g := fun θ => ‖G θ‖) (ae_of_all _ fun x => norm_nonneg _)
    (ae_of_all _ fun x => norm_nonneg _) (by simpa using hDmem.norm) (by simpa using hGmem.norm)
  have hLD := lpnorm_toReal β hβ0 hDmem
  have hLG := lpnorm_toReal p hp0 hGmem
  have hGb := hC0 q (epsS a) (epsS_abs a) φ p hp1
  rw [hLG] at hGb
  simp only [one_div] at h2
  rw [← hLD] at h2
  have hLDnn : 0 ≤ (eLpNorm D (ENNReal.ofReal β) μ).toReal := ENNReal.toReal_nonneg
  have h3 : Real.pi * ∑ j ∈ Icc 1 q, (j:ℝ) ^ m * |a j| ≤ (eLpNorm D (ENNReal.ofReal β) μ).toReal * (C0 * p) := by
    rw [← hkey, hint]
    refine h1.trans (h2.trans ?_)
    exact mul_le_mul_of_nonneg_left hGb hLDnn
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hpi]
  nlinarith [h3]

lemma F_eq (q : ℕ) (a : ℕ → ℝ) (K : ℝ) (hK : 0 < K) (θ : ℝ) :
    ∑ j ∈ range (q + 1), a j * (Chebyshev.T ℝ j).eval (K * Real.cos θ / K)
      = ∑ j ∈ range (q + 1), a j * Real.cos (j * θ) := by
  refine sum_congr rfl fun j _ => ?_
  rw [mul_div_cancel_left₀ _ hK.ne', Chebyshev.T_real_cos]
  simp

lemma int_F (q : ℕ) (a : ℕ → ℝ) :
    ∫ θ in (0:ℝ)..2 * Real.pi, ∑ j ∈ range (q + 1), a j * Real.cos (j * θ) = 2 * Real.pi * a 0 := by
  rw [intervalIntegral.integral_finsetSum (fun j _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
  have : ∀ j ∈ range (q + 1), ∫ θ in (0:ℝ)..2 * Real.pi, a j * Real.cos (j * θ)
      = if j = 0 then 2 * Real.pi * a 0 else 0 := by
    intro j _
    rw [intervalIntegral.integral_const_mul]
    have := int_cos_phase (j:ℤ) 0
    simp only [Int.cast_natCast, add_zero, Int.natCast_eq_zero, Real.cos_zero, mul_one] at this
    rw [this]
    by_cases h : j = 0
    · subst h; simp; ring
    · simp [h]
  rw [sum_congr rfl this, sum_ite_eq' (range (q + 1)) 0]
  simp

lemma part_i (q : ℕ) (a : ℕ → ℝ) (K : ℝ) (hK : 0 < K) :
    |a 0| ≤ sSup ((fun x => |∑ j ∈ range (q + 1), a j * (Chebyshev.T ℝ j).eval (x / K)|) ''
      Set.Icc (-K) K) := by
  set h : ℝ → ℝ := fun x => ∑ j ∈ range (q + 1), a j * (Chebyshev.T ℝ j).eval (x / K) with hh
  have hcont : Continuous h := by
    rw [hh]
    refine continuous_finset_sum _ fun j _ => continuous_const.mul ?_
    exact (Polynomial.continuous _).comp (continuous_id.div_const K)
  have hbdd : BddAbove ((fun x => |h x|) '' Set.Icc (-K) K) :=
    (isCompact_Icc.image (hcont.abs)).bddAbove
  set S := sSup ((fun x => |h x|) '' Set.Icc (-K) K) with hS
  have hsup : ∀ θ : ℝ, |∑ j ∈ range (q + 1), a j * Real.cos (j * θ)| ≤ S := by
    intro θ
    rw [← F_eq q a K hK θ]
    apply le_csSup hbdd
    refine ⟨K * Real.cos θ, ⟨?_, ?_⟩, rfl⟩
    · nlinarith [Real.neg_one_le_cos θ]
    · nlinarith [Real.cos_le_one θ]
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * Real.pi)
    (f := fun θ => ∑ j ∈ range (q + 1), a j * Real.cos (j * θ)) (C := S) (fun x _ => by
      rw [Real.norm_eq_abs]; exact hsup x)
  have hpi : 0 < 2 * Real.pi := by positivity
  rw [int_F, Real.norm_eq_abs, abs_mul, abs_of_pos hpi, sub_zero, abs_of_pos hpi] at hI
  nlinarith [hI]


end StrongConvS4.L44


namespace StrongConv

theorem abs_coeff_zero_le_and_sum_le_lpNormCircle_dev :
    ∃ C : ℝ, ∀ (q : ℕ) (a : ℕ → ℝ) (K : ℝ), 0 < K →
      |a 0| ≤ cNorm 0 (fun x => ∑ j ∈ Finset.range (q + 1),
          a j * (Chebyshev.T ℝ j).eval (x / K)) (-K) K ∧
      ∀ (m : ℕ) (β : ℝ), 1 < β →
        ∑ j ∈ Finset.Icc 1 q, (j : ℝ) ^ m * |a j| ≤
          C * conjExp β * lpNormCircle β (iteratedDeriv (m + 1) (fun θ =>
            ∑ j ∈ Finset.range (q + 1), a j * (Chebyshev.T ℝ j).eval (K * Real.cos θ / K))) := by
  obtain ⟨C0, hC0⟩ := StrongConvS4.L44.G_lp_bound
  refine ⟨C0 / Real.pi, fun q a K hK => ⟨?_, fun m β hβ => ?_⟩⟩
  · have := StrongConvS4.L44.part_i q a K hK
    simpa [cNorm, supOn] using this
  · have hF : (fun θ : ℝ => ∑ j ∈ Finset.range (q + 1), a j * (Chebyshev.T ℝ j).eval (K * Real.cos θ / K))
        = fun θ => ∑ j ∈ Finset.range (q + 1), a j * Real.cos (j * θ) :=
      funext fun θ => StrongConvS4.L44.F_eq q a K hK θ
    rw [hF, StrongConvS4.L44.iter_F]
    unfold conjExp lpNormCircle
    exact StrongConvS4.L44.partii_core C0 hC0 q a m β hβ

end StrongConv

end
end

section
open Polynomial
open StrongConv

theorem solution :
    ∃ C : ℝ, ∀ (q : ℕ) (a : ℕ → ℝ) (K : ℝ), 0 < K →
      |a 0| ≤ cNorm 0 (fun x => ∑ j ∈ Finset.range (q + 1),
          a j * (Chebyshev.T ℝ j).eval (x / K)) (-K) K ∧
      ∀ (m : ℕ) (β : ℝ), 1 < β →
        ∑ j ∈ Finset.Icc 1 q, (j : ℝ) ^ m * |a j| ≤
          C * conjExp β * lpNormCircle β (iteratedDeriv (m + 1) (fun θ =>
            ∑ j ∈ Finset.range (q + 1), a j * (Chebyshev.T ℝ j).eval (K * Real.cos θ / K))) := by
  apply StrongConv.abs_coeff_zero_le_and_sum_le_lpNormCircle_dev <;> assumption

end
