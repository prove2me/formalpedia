-- Prove2me | solution 1 for PriceQualityService.Oligopoly.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T05:36:49.633974+00:00
-- url     : https://prove2.me/submissions/c79c1723-3334-4b79-a2c0-0db99f869e8f

import Mathlib
import Definitions.Def_PriceQualityService_Oligopoly_Model

set_option autoImplicit false

namespace PQSProof

open Finset PriceQualityService.Oligopoly

/-! ### The root of `m - 1 = C * exp (-m)` -/

lemma mroot_exists {C : ℝ} (hC : 0 ≤ C) : ∃ m : ℝ, m - 1 = C * Real.exp (-m) := by
  have hcont : ContinuousOn (fun m : ℝ => m - 1 - C * Real.exp (-m)) (Set.Icc 1 (1 + C)) := by
    fun_prop
  have h1 : (fun m : ℝ => m - 1 - C * Real.exp (-m)) 1 ≤ 0 := by
    simp only
    have := Real.exp_pos (-1)
    nlinarith
  have h2 : 0 ≤ (fun m : ℝ => m - 1 - C * Real.exp (-m)) (1 + C) := by
    simp only
    have : Real.exp (-(1 + C)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith
  obtain ⟨m, _, hm⟩ := intermediate_value_Icc (by linarith) hcont ⟨h1, h2⟩
  exact ⟨m, by simp only at hm; linarith⟩

noncomputable def mroot (C : ℝ) : ℝ :=
  if h : 0 ≤ C then Classical.choose (mroot_exists h) else 1

lemma mroot_spec {C : ℝ} (hC : 0 ≤ C) : mroot C - 1 = C * Real.exp (-mroot C) := by
  unfold mroot
  rw [dif_pos hC]
  exact Classical.choose_spec (mroot_exists hC)

lemma one_le_mroot {C : ℝ} (hC : 0 ≤ C) : 1 ≤ mroot C := by
  have h := mroot_spec hC
  have : 0 ≤ C * Real.exp (-mroot C) := mul_nonneg hC (Real.exp_pos _).le
  linarith

lemma mroot_le {C : ℝ} (hC : 0 ≤ C) : mroot C ≤ 1 + C := by
  have h := mroot_spec hC
  have h1 := one_le_mroot hC
  have : Real.exp (-mroot C) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have : C * Real.exp (-mroot C) ≤ C := by nlinarith
  linarith

lemma mroot_mono {C C' : ℝ} (hC : 0 ≤ C) (h : C ≤ C') : mroot C ≤ mroot C' := by
  by_contra hlt
  push_neg at hlt
  have h1 := mroot_spec hC
  have h2 := mroot_spec (hC.trans h)
  have e : Real.exp (-mroot C) < Real.exp (-mroot C') := Real.exp_lt_exp.mpr (by linarith)
  have e1 : C * Real.exp (-mroot C) ≤ C * Real.exp (-mroot C') :=
    mul_le_mul_of_nonneg_left e.le hC
  have e2 : C * Real.exp (-mroot C') ≤ C' * Real.exp (-mroot C') :=
    mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
  linarith

lemma mroot_K {G K : ℝ} (hK : 0 < K) :
    (mroot (Real.exp G / K) - 1) * K = Real.exp (G - mroot (Real.exp G / K)) := by
  rw [mroot_spec (div_nonneg (Real.exp_pos _).le hK.le), Real.exp_sub, Real.exp_neg]
  field_simp

/-! ### The core inequality `exp (g - m) * (m - θ + 1) ≤ exp (G - θ)` -/

lemma core_le (g G m θ : ℝ) (hg : g ≤ G) :
    Real.exp (g - m) * (m - θ + 1) ≤ Real.exp (G - θ) := by
  have h1 := Real.add_one_le_exp (m - θ)
  have h2 : Real.exp (g - m) * Real.exp (m - θ) = Real.exp (g - θ) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : Real.exp (g - θ) ≤ Real.exp (G - θ) := Real.exp_le_exp.mpr (by linarith)
  have h4 := Real.exp_pos (g - m)
  have h5 := mul_le_mul_of_nonneg_left h1 h4.le
  have h6 : Real.exp (g - m) * (m - θ + 1) = Real.exp (g - m) * (m - θ + 1) := rfl
  linarith

lemma core_eq (g G m θ : ℝ) (hg : g ≤ G)
    (h : Real.exp (G - θ) ≤ Real.exp (g - m) * (m - θ + 1)) : m = θ ∧ g = G := by
  have h4 := Real.exp_pos (g - m)
  have h2 : Real.exp (g - m) * Real.exp (m - θ) = Real.exp (g - θ) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : Real.exp (g - θ) ≤ Real.exp (G - θ) := Real.exp_le_exp.mpr (by linarith)
  have hm : m = θ := by
    by_contra hne
    have h1 := Real.add_one_lt_exp (sub_ne_zero.mpr hne)
    have h5 := mul_lt_mul_of_pos_left h1 h4
    linarith
  refine ⟨hm, ?_⟩
  rw [hm, sub_self, zero_add, mul_one] at h
  have := Real.exp_le_exp.mp h
  linarith

/-! ### One firm's problem -/

lemma firm_bound {K M g G R : ℝ} (hK : 0 < K) (hg : g ≤ G)
    (hR : (R - 1) * K = Real.exp (G - R)) :
    M * Real.exp (g - M) / (K + Real.exp (g - M)) ≤ R - 1 := by
  have hx := Real.exp_pos (g - M)
  rw [div_le_iff₀ (by linarith)]
  have := core_le g G M R hg
  have e : (R - 1) * (K + Real.exp (g - M)) = (R - 1) * K + Real.exp (g - M) * (R - 1) := by ring
  have e2 : Real.exp (g - M) * (M - R + 1) = M * Real.exp (g - M) - Real.exp (g - M) * (R - 1) := by
    ring
  linarith

lemma firm_eq {K M g G R : ℝ} (hK : 0 < K) (hg : g ≤ G)
    (hR : (R - 1) * K = Real.exp (G - R))
    (h : R - 1 ≤ M * Real.exp (g - M) / (K + Real.exp (g - M))) : M = R ∧ g = G := by
  have hx := Real.exp_pos (g - M)
  rw [le_div_iff₀ (by linarith)] at h
  apply core_eq g G M R hg
  have e : (R - 1) * (K + Real.exp (g - M)) = (R - 1) * K + Real.exp (g - M) * (R - 1) := by ring
  have e2 : Real.exp (g - M) * (M - R + 1) = M * Real.exp (g - M) - Real.exp (g - M) * (R - 1) := by
    ring
  linarith

lemma firm_achieve {K R G : ℝ} (hK : 0 < K) (hR1 : 1 ≤ R)
    (hR : (R - 1) * K = Real.exp (G - R)) :
    R * Real.exp (G - R) / (K + Real.exp (G - R)) = R - 1 := by
  rw [← hR]
  have : K + (R - 1) * K = R * K := by ring
  rw [this, div_eq_iff (mul_pos (by linarith) hK).ne']
  ring

/-! ### Quality and duration -/

noncomputable def hf {N : ℕ} (α a b c s : Fin N → ℝ) (i : Fin N) (τ : ℝ) : ℝ :=
  (α i + b i * τ) ^ 2 / (4 * c i) + τ * (s i - a i)

def gf {N : ℕ} (α a b c s : Fin N → ℝ) (i : Fin N) (q τ : ℝ) : ℝ :=
  -c i * q ^ 2 + (α i + b i * τ) * q + τ * (s i - a i)

noncomputable def Topt {N : ℕ} (α a b c s : Fin N → ℝ) (ts tl : ℝ) (i : Fin N) : ℝ :=
  if hf α a b c s i ts < hf α a b c s i tl then tl else ts

noncomputable def Qopt {N : ℕ} (α a b c s : Fin N → ℝ) (ts tl : ℝ) (i : Fin N) : ℝ :=
  (α i + b i * Topt α a b c s ts tl i) / (2 * c i)

noncomputable def Gopt {N : ℕ} (α a b c s : Fin N → ℝ) (ts tl : ℝ) (i : Fin N) : ℝ :=
  hf α a b c s i (Topt α a b c s ts tl i)

section quality

variable {N : ℕ} (α a b c s : Fin N → ℝ) (ts tl : ℝ)

lemma hf_eq_DI (i : Fin N) (hc : 0 < c i) (τ : ℝ) :
    hf α a b c s i τ = durationIndex α a b c s i τ + α i ^ 2 / (4 * c i) := by
  unfold hf durationIndex
  have : c i ≠ 0 := hc.ne'
  field_simp
  ring

lemma hf_sub_gf (i : Fin N) (hc : 0 < c i) (q τ : ℝ) :
    hf α a b c s i τ - gf α a b c s i q τ = c i * (q - (α i + b i * τ) / (2 * c i)) ^ 2 := by
  unfold hf gf
  have : c i ≠ 0 := hc.ne'
  field_simp
  ring

lemma hf_convex (i : Fin N) (hc : 0 < c i) (τ : ℝ) :
    (tl - ts) * hf α a b c s i τ = (tl - τ) * hf α a b c s i ts + (τ - ts) * hf α a b c s i tl
      - b i ^ 2 / (4 * c i) * ((τ - ts) * (tl - τ) * (tl - ts)) := by
  unfold hf
  have : c i ≠ 0 := hc.ne'
  field_simp
  ring

lemma Topt_mem (hst : ts < tl) (i : Fin N) : Topt α a b c s ts tl i ∈ Set.Icc ts tl := by
  unfold Topt
  split_ifs
  · exact ⟨hst.le, le_refl _⟩
  · exact ⟨le_refl _, hst.le⟩

lemma hf_le_T (i : Fin N) (hc : 0 < c i) (hst : ts < tl)
    (hne : hf α a b c s i ts ≠ hf α a b c s i tl) {τ : ℝ} (hτ : τ ∈ Set.Icc ts tl) :
    hf α a b c s i τ ≤ hf α a b c s i (Topt α a b c s ts tl i) ∧
      (hf α a b c s i (Topt α a b c s ts tl i) ≤ hf α a b c s i τ →
        τ = Topt α a b c s ts tl i) := by
  obtain ⟨h1, h2⟩ := hτ
  have key := hf_convex α a b c s ts tl i hc τ
  have hnn : 0 ≤ b i ^ 2 / (4 * c i) * ((τ - ts) * (tl - τ) * (tl - ts)) := by
    apply mul_nonneg (div_nonneg (sq_nonneg _) (by linarith [hc]))
    apply mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have hd : 0 < tl - ts := by linarith
  unfold Topt
  split_ifs with hlt
  · have hA : (tl - τ) * hf α a b c s i ts ≤ (tl - τ) * hf α a b c s i tl :=
      mul_le_mul_of_nonneg_left hlt.le (by linarith)
    have hle : (tl - ts) * hf α a b c s i τ ≤ (tl - ts) * hf α a b c s i tl := by nlinarith
    refine ⟨le_of_mul_le_mul_left hle hd, fun h => ?_⟩
    by_contra hneq
    have hlt' : τ < tl := lt_of_le_of_ne h2 hneq
    have hA' : (tl - τ) * hf α a b c s i ts < (tl - τ) * hf α a b c s i tl :=
      mul_lt_mul_of_pos_left hlt (by linarith)
    have : (tl - ts) * hf α a b c s i τ < (tl - ts) * hf α a b c s i tl := by nlinarith
    have : (tl - ts) * hf α a b c s i tl ≤ (tl - ts) * hf α a b c s i τ :=
      mul_le_mul_of_nonneg_left h hd.le
    linarith
  · have hlt2 : hf α a b c s i tl < hf α a b c s i ts := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne)
    have hA : (τ - ts) * hf α a b c s i tl ≤ (τ - ts) * hf α a b c s i ts :=
      mul_le_mul_of_nonneg_left hlt2.le (by linarith)
    have hle : (tl - ts) * hf α a b c s i τ ≤ (tl - ts) * hf α a b c s i ts := by nlinarith
    refine ⟨le_of_mul_le_mul_left hle hd, fun h => ?_⟩
    by_contra hneq
    have hlt' : ts < τ := lt_of_le_of_ne h1 (Ne.symm hneq)
    have hA' : (τ - ts) * hf α a b c s i tl < (τ - ts) * hf α a b c s i ts :=
      mul_lt_mul_of_pos_left hlt2 (by linarith)
    have : (tl - ts) * hf α a b c s i τ < (tl - ts) * hf α a b c s i ts := by nlinarith
    have : (tl - ts) * hf α a b c s i ts ≤ (tl - ts) * hf α a b c s i τ :=
      mul_le_mul_of_nonneg_left h hd.le
    linarith

lemma g_le (i : Fin N) (hc : 0 < c i) (hst : ts < tl)
    (hne : hf α a b c s i ts ≠ hf α a b c s i tl) {q τ : ℝ} (hτ : τ ∈ Set.Icc ts tl) :
    gf α a b c s i q τ ≤ Gopt α a b c s ts tl i ∧
      (Gopt α a b c s ts tl i ≤ gf α a b c s i q τ →
        τ = Topt α a b c s ts tl i ∧ q = Qopt α a b c s ts tl i) := by
  have h1 := hf_sub_gf α a b c s i hc q τ
  have h2 : 0 ≤ c i * (q - (α i + b i * τ) / (2 * c i)) ^ 2 :=
    mul_nonneg hc.le (sq_nonneg _)
  obtain ⟨hle, heq⟩ := hf_le_T α a b c s ts tl i hc hst hne hτ
  unfold Gopt
  refine ⟨by linarith, fun h => ?_⟩
  have hτT : τ = Topt α a b c s ts tl i := heq (by linarith)
  refine ⟨hτT, ?_⟩
  have h0 : c i * (q - (α i + b i * τ) / (2 * c i)) ^ 2 = 0 := by linarith
  rcases mul_eq_zero.mp h0 with h3 | h3
  · exact absurd h3 hc.ne'
  · have := pow_eq_zero_iff (two_ne_zero) |>.mp h3
    unfold Qopt
    rw [← hτT]
    linarith

lemma Gopt_achieved (i : Fin N) (hc : 0 < c i) :
    gf α a b c s i (Qopt α a b c s ts tl i) (Topt α a b c s ts tl i) = Gopt α a b c s ts tl i := by
  have h1 := hf_sub_gf α a b c s i hc (Qopt α a b c s ts tl i) (Topt α a b c s ts tl i)
  unfold Gopt
  unfold Qopt at h1 ⊢
  rw [sub_self] at h1
  simp at h1
  linarith

end quality

/-! ### Oligopoly profiles -/

noncomputable def Kx {N : ℕ} (α s : Fin N → ℝ) (x : Fin N → ℝ × ℝ × ℝ) (i : Fin N) : ℝ :=
  1 + ∑ j ∈ univ.erase i, Real.exp (α j * (x j).2.1 - (x j).1 + (x j).2.2 * s j)

def Mx {N : ℕ} (a b c : Fin N → ℝ) (x : Fin N → ℝ × ℝ × ℝ) (i : Fin N) : ℝ :=
  (x i).1 - c i * (x i).2.1 ^ 2 - (x i).2.2 * (a i - b i * (x i).2.1)

section olig

variable {N : ℕ} (α a b c s : Fin N → ℝ) (ts tl : ℝ)

lemma Kx_pos (x : Fin N → ℝ × ℝ × ℝ) (i : Fin N) : 1 ≤ Kx α s x i := by
  unfold Kx
  have : 0 ≤ ∑ j ∈ univ.erase i, Real.exp (α j * (x j).2.1 - (x j).1 + (x j).2.2 * s j) := by
    positivity
  linarith

lemma expo (x : Fin N → ℝ × ℝ × ℝ) (j : Fin N) :
    α j * (x j).2.1 - (x j).1 + (x j).2.2 * s j =
      gf α a b c s j (x j).2.1 (x j).2.2 - Mx a b c x j := by
  unfold gf Mx; ring

lemma firmProfit_eq (x : Fin N → ℝ × ℝ × ℝ) (i : Fin N) :
    firmProfit α a b c s (prices x) (qualities x) (durations x) i =
      Mx a b c x i * Real.exp (gf α a b c s i (x i).2.1 (x i).2.2 - Mx a b c x i) /
        (Kx α s x i + Real.exp (gf α a b c s i (x i).2.1 (x i).2.2 - Mx a b c x i)) := by
  have hsum : (∑ j, Real.exp (α j * (x j).2.1 - (x j).1 + (x j).2.2 * s j)) =
      Real.exp (α i * (x i).2.1 - (x i).1 + (x i).2.2 * s i) +
        ∑ j ∈ univ.erase i, Real.exp (α j * (x j).2.1 - (x j).1 + (x j).2.2 * s j) :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  simp only [firmProfit, PriceQualityService.Joint.markup, PriceQualityService.Joint.choiceProb,
    PriceQualityService.Joint.attraction, prices, qualities, durations]
  rw [hsum, expo α a b c s x i]
  unfold Kx Mx
  ring

lemma Kx_update (x : Fin N → ℝ × ℝ × ℝ) (i : Fin N) (y : ℝ × ℝ × ℝ) :
    Kx α s (Function.update x i y) i = Kx α s x i := by
  unfold Kx
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

lemma firmProfit_update (x : Fin N → ℝ × ℝ × ℝ) (i : Fin N) (y : ℝ × ℝ × ℝ) :
    firmProfit α a b c s (prices (Function.update x i y)) (qualities (Function.update x i y))
        (durations (Function.update x i y)) i =
      (y.1 - c i * y.2.1 ^ 2 - y.2.2 * (a i - b i * y.2.1)) *
          Real.exp (gf α a b c s i y.2.1 y.2.2 - (y.1 - c i * y.2.1 ^ 2 - y.2.2 * (a i - b i * y.2.1))) /
        (Kx α s x i + Real.exp (gf α a b c s i y.2.1 y.2.2 -
          (y.1 - c i * y.2.1 ^ 2 - y.2.2 * (a i - b i * y.2.1)))) := by
  rw [firmProfit_eq, Kx_update]
  have hu : Function.update x i y i = y := Function.update_self i y x
  unfold Mx
  rw [hu]

lemma eq_char (hc : ∀ i, 0 < c i) (hst : ts < tl)
    (hne : ∀ i, hf α a b c s i ts ≠ hf α a b c s i tl) (x : Fin N → ℝ × ℝ × ℝ) :
    IsOligopolyEquilibrium α a b c s ts tl x ↔
      ∀ i, (x i).2.2 = Topt α a b c s ts tl i ∧ (x i).2.1 = Qopt α a b c s ts tl i ∧
        Mx a b c x i = mroot (Real.exp (Gopt α a b c s ts tl i) / Kx α s x i) := by
  constructor
  · rintro ⟨hfeas, hbest⟩ i
    have hK : 0 < Kx α s x i := by linarith [Kx_pos α s x i]
    have hR := mroot_K (G := Gopt α a b c s ts tl i) hK
    have hR1 : 1 ≤ mroot (Real.exp (Gopt α a b c s ts tl i) / Kx α s x i) :=
      one_le_mroot (div_nonneg (Real.exp_pos _).le hK.le)
    set R := mroot (Real.exp (Gopt α a b c s ts tl i) / Kx α s x i) with hRdef
    set y : ℝ × ℝ × ℝ := (R + c i * Qopt α a b c s ts tl i ^ 2 +
      Topt α a b c s ts tl i * (a i - b i * Qopt α a b c s ts tl i),
      Qopt α a b c s ts tl i, Topt α a b c s ts tl i) with hydef
    have hy : y ∈ {y : ℝ × ℝ × ℝ | y.2.2 ∈ Set.Icc ts tl} := Topt_mem α a b c s ts tl hst i
    have h1 := hbest i y hy
    have hm : y.1 - c i * y.2.1 ^ 2 - y.2.2 * (a i - b i * y.2.1) = R := by
      simp only [hydef]; ring
    have hg : gf α a b c s i y.2.1 y.2.2 = Gopt α a b c s ts tl i :=
      Gopt_achieved α a b c s ts tl i (hc i)
    have hdev : firmProfit α a b c s (prices (Function.update x i y))
        (qualities (Function.update x i y)) (durations (Function.update x i y)) i = R - 1 := by
      rw [firmProfit_update, hm, hg]
      exact firm_achieve hK hR1 hR
    simp only at h1
    rw [hdev, firmProfit_eq] at h1
    have hxi : (x i).2.2 ∈ Set.Icc ts tl := hfeas i
    have hgle := (g_le α a b c s ts tl i (hc i) hst (hne i) (q := (x i).2.1) hxi)
    obtain ⟨hM, hG⟩ := firm_eq hK hgle.1 hR h1
    obtain ⟨ht, hq⟩ := hgle.2 (le_of_eq hG.symm)
    exact ⟨ht, hq, hM⟩
  · intro h
    refine ⟨fun i => ?_, fun i y hy => ?_⟩
    · show (x i).2.2 ∈ Set.Icc ts tl
      rw [(h i).1]
      exact Topt_mem α a b c s ts tl hst i
    · have hK : 0 < Kx α s x i := by linarith [Kx_pos α s x i]
      have hR := mroot_K (G := Gopt α a b c s ts tl i) hK
      have hR1 : 1 ≤ mroot (Real.exp (Gopt α a b c s ts tl i) / Kx α s x i) :=
        one_le_mroot (div_nonneg (Real.exp_pos _).le hK.le)
      have hy' : y.2.2 ∈ Set.Icc ts tl := hy
      show firmProfit α a b c s (prices (Function.update x i y)) (qualities (Function.update x i y))
        (durations (Function.update x i y)) i ≤
          firmProfit α a b c s (prices x) (qualities x) (durations x) i
      rw [firmProfit_update, firmProfit_eq]
      have hgx : gf α a b c s i (x i).2.1 (x i).2.2 = Gopt α a b c s ts tl i := by
        rw [(h i).1, (h i).2.1]; exact Gopt_achieved α a b c s ts tl i (hc i)
      rw [hgx, (h i).2.2, firm_achieve hK hR1 hR]
      exact firm_bound hK (g_le α a b c s ts tl i (hc i) hst (hne i) hy').1 hR

lemma Kx_char (hc : ∀ i, 0 < c i) (x : Fin N → ℝ × ℝ × ℝ)
    (h : ∀ j, (x j).2.2 = Topt α a b c s ts tl j ∧ (x j).2.1 = Qopt α a b c s ts tl j)
    (i : Fin N) :
    Kx α s x i = 1 + ∑ j ∈ univ.erase i, Real.exp (Gopt α a b c s ts tl j - Mx a b c x j) := by
  unfold Kx
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [expo α a b c s x j, (h j).1, (h j).2, Gopt_achieved α a b c s ts tl j (hc j)]

end olig

/-! ### The markup system -/

section markup

variable {N : ℕ} (G : Fin N → ℝ)

lemma mk_facts (m : Fin N → ℝ)
    (hm : ∀ i, (m i - 1) * (1 + ∑ j ∈ univ.erase i, Real.exp (G j - m j)) = Real.exp (G i - m i))
    (i : Fin N) :
    1 < m i ∧ (m i - 1) * (1 + ∑ j, Real.exp (G j - m j)) = m i * Real.exp (G i - m i) := by
  have hs : (∑ j, Real.exp (G j - m j)) =
      Real.exp (G i - m i) + ∑ j ∈ univ.erase i, Real.exp (G j - m j) :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  have hE : 0 ≤ ∑ j ∈ univ.erase i, Real.exp (G j - m j) := by positivity
  have hA := Real.exp_pos (G i - m i)
  have h := hm i
  refine ⟨?_, ?_⟩
  · by_contra hle
    push_neg at hle
    have : (m i - 1) * (1 + ∑ j ∈ univ.erase i, Real.exp (G j - m j)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    linarith
  · rw [hs]
    linear_combination h

lemma mk_sum (m : Fin N → ℝ)
    (hm : ∀ i, (m i - 1) * (1 + ∑ j ∈ univ.erase i, Real.exp (G j - m j)) = Real.exp (G i - m i)) :
    ∑ i, (1 - 1 / m i) = 1 - 1 / (1 + ∑ j, Real.exp (G j - m j)) := by
  have hY : 0 < 1 + ∑ j, Real.exp (G j - m j) := by positivity
  have hterm : ∀ i, 1 - 1 / m i = Real.exp (G i - m i) / (1 + ∑ j, Real.exp (G j - m j)) := by
    intro i
    obtain ⟨h1, h2⟩ := mk_facts G m hm i
    have hm0 : m i ≠ 0 := by linarith
    rw [show (1 : ℝ) - 1 / m i = (m i - 1) / m i by rw [sub_div, div_self hm0]]
    rw [div_eq_div_iff hm0 hY.ne']
    linear_combination h2
  rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.sum_div]
  field_simp
  ring

lemma mk_cmp {G0 m m' Y Y' : ℝ} (hm1 : 1 < m) (hm1' : 1 < m') (hY : 0 < Y) (hY' : 0 < Y')
    (h : (m - 1) * Y = m * Real.exp (G0 - m)) (h' : (m' - 1) * Y' = m' * Real.exp (G0 - m'))
    (hYY : Y ≤ Y') : m' ≤ m := by
  by_contra hlt
  push_neg at hlt
  have e : Real.exp (G0 - m') < Real.exp (G0 - m) := Real.exp_lt_exp.mpr (by linarith)
  have h1 : m * m' * Real.exp (G0 - m') < m * m' * Real.exp (G0 - m) :=
    mul_lt_mul_of_pos_left e (by positivity)
  have h2 : (m - 1) * m' * Y ≤ (m - 1) * m' * Y' :=
    mul_le_mul_of_nonneg_left hYY (by positivity)
  have e1 : (m' - 1) * m * Y' = m * m' * Real.exp (G0 - m') := by
    linear_combination m * h'
  have e2 : (m - 1) * m' * Y = m * m' * Real.exp (G0 - m) := by
    linear_combination m' * h
  have h3 : (m' - 1) * m * Y' < (m - 1) * m' * Y' := by linarith
  have h4 : 0 < (m' - m) * Y' := mul_pos (by linarith) hY'
  nlinarith

lemma mk_uniq_le (m m' : Fin N → ℝ)
    (hm : ∀ i, (m i - 1) * (1 + ∑ j ∈ univ.erase i, Real.exp (G j - m j)) = Real.exp (G i - m i))
    (hm' : ∀ i, (m' i - 1) * (1 + ∑ j ∈ univ.erase i, Real.exp (G j - m' j)) =
      Real.exp (G i - m' i))
    (hYY : 1 + ∑ j, Real.exp (G j - m j) ≤ 1 + ∑ j, Real.exp (G j - m' j)) : m = m' := by
  have hY : 0 < 1 + ∑ j, Real.exp (G j - m j) := by positivity
  have hY' : 0 < 1 + ∑ j, Real.exp (G j - m' j) := by positivity
  have aux : ∀ (u v : Fin N → ℝ),
      (∀ i, (u i - 1) * (1 + ∑ j ∈ univ.erase i, Real.exp (G j - u j)) = Real.exp (G i - u i)) →
      (∀ i, (v i - 1) * (1 + ∑ j ∈ univ.erase i, Real.exp (G j - v j)) = Real.exp (G i - v i)) →
      1 + ∑ j, Real.exp (G j - u j) ≤ 1 + ∑ j, Real.exp (G j - v j) → ∀ i, v i ≤ u i := by
    intro u v hu hv huv i
    obtain ⟨hu1, hu2⟩ := mk_facts G u hu i
    obtain ⟨hv1, hv2⟩ := mk_facts G v hv i
    exact mk_cmp hu1 hv1 (by positivity) (by positivity) hu2 hv2 huv
  have h1 := aux m m' hm hm' hYY
  have hs : ∑ i, (1 - 1 / m' i) ≤ ∑ i, (1 - 1 / m i) := by
    apply Finset.sum_le_sum
    intro i _
    have hp : 0 < m' i := by linarith [(mk_facts G m' hm' i).1]
    have := one_div_le_one_div_of_le hp (h1 i)
    linarith
  rw [mk_sum G m hm, mk_sum G m' hm'] at hs
  have hYY' : 1 + ∑ j, Real.exp (G j - m' j) ≤ 1 + ∑ j, Real.exp (G j - m j) := by
    have : 1 / (1 + ∑ j, Real.exp (G j - m j)) ≤ 1 / (1 + ∑ j, Real.exp (G j - m' j)) := by
      linarith
    exact (one_div_le_one_div hY hY').mp this
  have h2 := aux m' m hm' hm hYY'
  funext i
  exact le_antisymm (h2 i) (h1 i)

lemma mk_uniq (m m' : Fin N → ℝ)
    (hm : ∀ i, (m i - 1) * (1 + ∑ j ∈ univ.erase i, Real.exp (G j - m j)) = Real.exp (G i - m i))
    (hm' : ∀ i, (m' i - 1) * (1 + ∑ j ∈ univ.erase i, Real.exp (G j - m' j)) =
      Real.exp (G i - m' i)) : m = m' := by
  rcases le_total (1 + ∑ j, Real.exp (G j - m j)) (1 + ∑ j, Real.exp (G j - m' j)) with h | h
  · exact mk_uniq_le G m m' hm hm' h
  · exact (mk_uniq_le G m' m hm' hm h).symm

lemma mk_exists : ∃ m : Fin N → ℝ, ∀ i,
    m i = mroot (Real.exp (G i) / (1 + ∑ j ∈ univ.erase i, Real.exp (G j - m j))) := by
  set B : ℝ := 1 + ∑ j, Real.exp (G j) with hB
  have : Fact ((1 : ℝ) ≤ B) := ⟨by
    have : 0 ≤ ∑ j, Real.exp (G j) := by positivity
    linarith⟩
  have Kpos : ∀ (m : Fin N → ℝ) (i : Fin N), 1 ≤ 1 + ∑ j ∈ univ.erase i, Real.exp (G j - m j) := by
    intro m i
    have : 0 ≤ ∑ j ∈ univ.erase i, Real.exp (G j - m j) := by positivity
    linarith
  have hC0 : ∀ (m : Fin N → ℝ) (i : Fin N),
      0 ≤ Real.exp (G i) / (1 + ∑ j ∈ univ.erase i, Real.exp (G j - m j)) :=
    fun m i => div_nonneg (Real.exp_pos _).le (by linarith [Kpos m i])
  have hmem : ∀ (m : Fin N → ℝ) (i : Fin N),
      mroot (Real.exp (G i) / (1 + ∑ j ∈ univ.erase i, Real.exp (G j - m j))) ∈
        Set.Icc (1 : ℝ) B := by
    intro m i
    refine ⟨one_le_mroot (hC0 m i), ?_⟩
    have h1 := mroot_le (hC0 m i)
    have h2 : Real.exp (G i) / (1 + ∑ j ∈ univ.erase i, Real.exp (G j - m j)) ≤ Real.exp (G i) :=
      div_le_self (Real.exp_pos _).le (Kpos m i)
    have h3 : Real.exp (G i) ≤ ∑ j, Real.exp (G j) :=
      Finset.single_le_sum (f := fun j => Real.exp (G j)) (fun j _ => (Real.exp_pos _).le)
        (Finset.mem_univ i)
    linarith
  let f : (Fin N → Set.Icc (1 : ℝ) B) →o (Fin N → Set.Icc (1 : ℝ) B) :=
    { toFun := fun m i => ⟨mroot (Real.exp (G i) /
          (1 + ∑ j ∈ univ.erase i, Real.exp (G j - (m j : ℝ)))), hmem (fun j => (m j : ℝ)) i⟩
      monotone' := by
        intro m m' hmm i
        show mroot _ ≤ mroot _
        apply mroot_mono (hC0 _ i)
        apply div_le_div_of_nonneg_left (Real.exp_pos _).le
          (by linarith [Kpos (fun j => (m' j : ℝ)) i])
        gcongr with j hj
        exact hmm j }
  refine ⟨fun i => (f.lfp i : ℝ), fun i => ?_⟩
  have := congrArg (fun z => (z i : ℝ)) f.map_lfp
  exact this.symm

end markup

/-! ### Monopoly -/

section mono

variable {N : ℕ} (α a b c s : Fin N → ℝ) (ts tl : ℝ)

lemma total_eq (p q t : Fin N → ℝ) :
    totalProfit α a b c s p q t =
      (∑ i, PriceQualityService.Joint.markup a b c p q t i *
          Real.exp (gf α a b c s i (q i) (t i) - PriceQualityService.Joint.markup a b c p q t i)) /
        (1 + ∑ j, Real.exp (gf α a b c s j (q j) (t j) -
          PriceQualityService.Joint.markup a b c p q t j)) := by
  have hx : ∀ j, α j * q j - p j + t j * s j =
      gf α a b c s j (q j) (t j) - PriceQualityService.Joint.markup a b c p q t j := by
    intro j; unfold gf PriceQualityService.Joint.markup; ring
  unfold totalProfit firmProfit PriceQualityService.Joint.choiceProb
    PriceQualityService.Joint.attraction
  simp only [hx]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

noncomputable def theta {N : ℕ} (α a b c s : Fin N → ℝ) (ts tl : ℝ) : ℝ :=
  mroot (∑ j, Real.exp (Gopt α a b c s ts tl j))

lemma theta_spec :
    theta α a b c s ts tl - 1 = ∑ j, Real.exp (Gopt α a b c s ts tl j - theta α a b c s ts tl) := by
  unfold theta
  rw [mroot_spec (by positivity), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Real.exp_sub, Real.exp_neg, div_eq_mul_inv]

lemma one_le_theta : 1 ≤ theta α a b c s ts tl := one_le_mroot (by positivity)

lemma mono_bound (hc : ∀ i, 0 < c i) (hst : ts < tl)
    (hne : ∀ i, hf α a b c s i ts ≠ hf α a b c s i tl) (p q t : Fin N → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc ts tl) :
    totalProfit α a b c s p q t ≤ theta α a b c s ts tl - 1 ∧
      (theta α a b c s ts tl - 1 ≤ totalProfit α a b c s p q t →
        ∀ i, t i = Topt α a b c s ts tl i ∧ q i = Qopt α a b c s ts tl i ∧
          PriceQualityService.Joint.markup a b c p q t i = theta α a b c s ts tl) := by
  set θ := theta α a b c s ts tl with hθdef
  have hθ := theta_spec α a b c s ts tl
  rw [← hθdef] at hθ
  set M := fun i => PriceQualityService.Joint.markup a b c p q t i with hMdef
  set g := fun i => gf α a b c s i (q i) (t i) with hgdef
  have hgle : ∀ i, g i ≤ Gopt α a b c s ts tl i ∧
      (Gopt α a b c s ts tl i ≤ g i → t i = Topt α a b c s ts tl i ∧ q i = Qopt α a b c s ts tl i) :=
    fun i => g_le α a b c s ts tl i (hc i) hst (hne i) (ht i)
  have hD : 0 < 1 + ∑ j, Real.exp (g j - M j) := by positivity
  have htot : totalProfit α a b c s p q t =
      (∑ i, M i * Real.exp (g i - M i)) / (1 + ∑ j, Real.exp (g j - M j)) := total_eq α a b c s p q t
  have e1 : ∑ i, Real.exp (g i - M i) * (M i - θ + 1) =
      ∑ i, M i * Real.exp (g i - M i) - (θ - 1) * ∑ i, Real.exp (g i - M i) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have e2 : (θ - 1) * (1 + ∑ j, Real.exp (g j - M j)) =
      (θ - 1) + (θ - 1) * ∑ j, Real.exp (g j - M j) := by ring
  have hterm : ∀ i ∈ (univ : Finset (Fin N)),
      0 ≤ Real.exp (Gopt α a b c s ts tl i - θ) - Real.exp (g i - M i) * (M i - θ + 1) := by
    intro i _
    have := core_le (g i) (Gopt α a b c s ts tl i) (M i) θ (hgle i).1
    linarith
  have hsum := Finset.sum_nonneg hterm
  rw [Finset.sum_sub_distrib] at hsum
  refine ⟨?_, fun h => ?_⟩
  · rw [htot, div_le_iff₀ hD]
    linarith
  · rw [htot, le_div_iff₀ hD] at h
    have hz : ∑ i, (Real.exp (Gopt α a b c s ts tl i - θ) -
        Real.exp (g i - M i) * (M i - θ + 1)) = 0 := by
      apply le_antisymm _ (Finset.sum_nonneg hterm)
      rw [Finset.sum_sub_distrib]
      linarith
    intro i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hz i (Finset.mem_univ i)
    obtain ⟨hM, hG⟩ := core_eq (g i) (Gopt α a b c s ts tl i) (M i) θ (hgle i).1 (by linarith)
    obtain ⟨h1, h2⟩ := (hgle i).2 (le_of_eq hG.symm)
    exact ⟨h1, h2, hM⟩

noncomputable def pstar {N : ℕ} (α a b c s : Fin N → ℝ) (ts tl : ℝ) (i : Fin N) : ℝ :=
  theta α a b c s ts tl + c i * Qopt α a b c s ts tl i ^ 2 +
    Topt α a b c s ts tl i * (a i - b i * Qopt α a b c s ts tl i)

lemma mono_value (hc : ∀ i, 0 < c i) :
    totalProfit α a b c s (pstar α a b c s ts tl) (Qopt α a b c s ts tl) (Topt α a b c s ts tl) =
      theta α a b c s ts tl - 1 := by
  rw [total_eq]
  have hmk : ∀ i, PriceQualityService.Joint.markup a b c (pstar α a b c s ts tl)
      (Qopt α a b c s ts tl) (Topt α a b c s ts tl) i = theta α a b c s ts tl := by
    intro i; unfold PriceQualityService.Joint.markup pstar; ring
  have hg : ∀ i, gf α a b c s i (Qopt α a b c s ts tl i) (Topt α a b c s ts tl i) =
      Gopt α a b c s ts tl i := fun i => Gopt_achieved α a b c s ts tl i (hc i)
  simp only [hmk, hg]
  rw [← Finset.mul_sum, ← theta_spec]
  have h1 := one_le_theta α a b c s ts tl
  rw [show 1 + (theta α a b c s ts tl - 1) = theta α a b c s ts tl by ring]
  field_simp

lemma mono_exists (hc : ∀ i, 0 < c i) (hst : ts < tl)
    (hne : ∀ i, hf α a b c s i ts ≠ hf α a b c s i tl) :
    IsMonopolyOptimum α a b c s ts tl (pstar α a b c s ts tl) (Qopt α a b c s ts tl)
      (Topt α a b c s ts tl) := by
  refine ⟨fun i => Topt_mem α a b c s ts tl hst i, fun p' q' t' ht' => ?_⟩
  rw [mono_value α a b c s ts tl hc]
  exact (mono_bound α a b c s ts tl hc hst hne p' q' t' ht').1

lemma R_le_theta {N : ℕ} (G : Fin N → ℝ) (i : Fin N) {K R θ : ℝ} (hK : 1 ≤ K) (hR1 : 1 ≤ R)
    (hR : (R - 1) * K = Real.exp (G i - R)) (hθ : θ - 1 = ∑ j, Real.exp (G j - θ)) : R ≤ θ := by
  by_contra hlt
  push_neg at hlt
  have e : Real.exp (G i - R) < Real.exp (G i - θ) := Real.exp_lt_exp.mpr (by linarith)
  have e2 : Real.exp (G i - θ) ≤ ∑ j, Real.exp (G j - θ) :=
    Finset.single_le_sum (f := fun j => Real.exp (G j - θ)) (fun j _ => (Real.exp_pos _).le)
      (Finset.mem_univ i)
  have e3 : R - 1 ≤ (R - 1) * K := by nlinarith
  linarith

end mono

noncomputable def xstar {N : ℕ} (a b c : Fin N → ℝ) (Q T m : Fin N → ℝ) : Fin N → ℝ × ℝ × ℝ :=
  fun i => (m i + c i * Q i ^ 2 + T i * (a i - b i * Q i), Q i, T i)

end PQSProof

open PriceQualityService.Oligopoly in
theorem solution {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) (ts tl : ℝ)
    (hst : ts < tl)
    (hnt : ∀ i, durationIndex α a b c s i ts ≠ durationIndex α a b c s i tl) :
    (∃! x : Fin N → ℝ × ℝ × ℝ, IsOligopolyEquilibrium α a b c s ts tl x) ∧
      (∃ p q t : Fin N → ℝ, IsMonopolyOptimum α a b c s ts tl p q t) ∧
      ∀ x : Fin N → ℝ × ℝ × ℝ, IsOligopolyEquilibrium α a b c s ts tl x →
        ∀ p q t : Fin N → ℝ, IsMonopolyOptimum α a b c s ts tl p q t →
          durations x = t ∧ qualities x = q ∧ ∀ i, prices x i ≤ p i := by
  have hne : ∀ i, PQSProof.hf α a b c s i ts ≠ PQSProof.hf α a b c s i tl := by
    intro i h
    apply hnt i
    rw [PQSProof.hf_eq_DI α a b c s i (hc i), PQSProof.hf_eq_DI α a b c s i (hc i)] at h
    linarith
  have eqmk : ∀ x, IsOligopolyEquilibrium α a b c s ts tl x →
      (∀ j, (x j).2.2 = PQSProof.Topt α a b c s ts tl j ∧
        (x j).2.1 = PQSProof.Qopt α a b c s ts tl j) ∧
      ∀ i, (PQSProof.Mx a b c x i - 1) *
          (1 + ∑ j ∈ Finset.univ.erase i,
            Real.exp (PQSProof.Gopt α a b c s ts tl j - PQSProof.Mx a b c x j)) =
        Real.exp (PQSProof.Gopt α a b c s ts tl i - PQSProof.Mx a b c x i) := by
    intro x hx
    have h := (PQSProof.eq_char α a b c s ts tl hc hst hne x).mp hx
    have hTQ : ∀ j, (x j).2.2 = PQSProof.Topt α a b c s ts tl j ∧
        (x j).2.1 = PQSProof.Qopt α a b c s ts tl j := fun j => ⟨(h j).1, (h j).2.1⟩
    refine ⟨hTQ, fun i => ?_⟩
    have hK := PQSProof.Kx_char α a b c s ts tl hc x hTQ i
    have hKpos : 0 < PQSProof.Kx α s x i := by linarith [PQSProof.Kx_pos α s x i]
    rw [← hK, (h i).2.2]
    exact PQSProof.mroot_K hKpos
  obtain ⟨m, hm⟩ := PQSProof.mk_exists (PQSProof.Gopt α a b c s ts tl)
  set x0 := PQSProof.xstar a b c (PQSProof.Qopt α a b c s ts tl) (PQSProof.Topt α a b c s ts tl) m
    with hx0def
  have hMx : ∀ j, PQSProof.Mx a b c x0 j = m j := by
    intro j; simp only [hx0def, PQSProof.Mx, PQSProof.xstar]; ring
  have hx0 : IsOligopolyEquilibrium α a b c s ts tl x0 := by
    rw [PQSProof.eq_char α a b c s ts tl hc hst hne x0]
    have hTQ : ∀ j, (x0 j).2.2 = PQSProof.Topt α a b c s ts tl j ∧
        (x0 j).2.1 = PQSProof.Qopt α a b c s ts tl j := fun j => ⟨rfl, rfl⟩
    intro i
    refine ⟨rfl, rfl, ?_⟩
    rw [PQSProof.Kx_char α a b c s ts tl hc x0 hTQ i]
    simp only [hMx]
    exact hm i
  refine ⟨⟨x0, hx0, fun y hy => ?_⟩, ⟨_, _, _, PQSProof.mono_exists α a b c s ts tl hc hst hne⟩,
    fun x hx p q t hopt => ?_⟩
  · obtain ⟨hTQy, hmy⟩ := eqmk y hy
    obtain ⟨hTQ0, hm0⟩ := eqmk x0 hx0
    have hmk := PQSProof.mk_uniq (PQSProof.Gopt α a b c s ts tl)
      (fun j => PQSProof.Mx a b c y j) (fun j => PQSProof.Mx a b c x0 j) hmy hm0
    funext i
    have hM := congrFun hmk i
    have ht : (y i).2.2 = (x0 i).2.2 := by rw [(hTQy i).1, (hTQ0 i).1]
    have hq : (y i).2.1 = (x0 i).2.1 := by rw [(hTQy i).2, (hTQ0 i).2]
    simp only [PQSProof.Mx] at hM
    rw [ht, hq] at hM
    exact Prod.ext (by linarith) (Prod.ext hq ht)
  · obtain ⟨hTQ, hmx⟩ := eqmk x hx
    have h := (PQSProof.eq_char α a b c s ts tl hc hst hne x).mp hx
    obtain ⟨ht, hmax⟩ := hopt
    have hv := hmax (PQSProof.pstar α a b c s ts tl) (PQSProof.Qopt α a b c s ts tl)
      (PQSProof.Topt α a b c s ts tl) (fun i => PQSProof.Topt_mem α a b c s ts tl hst i)
    rw [PQSProof.mono_value α a b c s ts tl hc] at hv
    have hb := (PQSProof.mono_bound α a b c s ts tl hc hst hne p q t ht).2 hv
    refine ⟨funext fun i => ?_, funext fun i => ?_, fun i => ?_⟩
    · show (x i).2.2 = t i
      rw [(hTQ i).1, (hb i).1]
    · show (x i).2.1 = q i
      rw [(hTQ i).2, (hb i).2.1]
    · show (x i).1 ≤ p i
      have hK1 := PQSProof.Kx_pos α s x i
      have hKpos : 0 < PQSProof.Kx α s x i := by linarith
      have hR := PQSProof.mroot_K (G := PQSProof.Gopt α a b c s ts tl i) hKpos
      have hR1 := PQSProof.one_le_mroot
        (div_nonneg (Real.exp_pos (PQSProof.Gopt α a b c s ts tl i)).le hKpos.le)
      have hle := PQSProof.R_le_theta (PQSProof.Gopt α a b c s ts tl) i hK1 hR1 hR
        (PQSProof.theta_spec α a b c s ts tl)
      rw [← (h i).2.2] at hle
      have hmk := (hb i).2.2
      unfold PriceQualityService.Joint.markup at hmk
      unfold PQSProof.Mx at hle
      rw [(hb i).1, (hb i).2.1] at hmk
      rw [(hTQ i).1, (hTQ i).2] at hle
      linarith
