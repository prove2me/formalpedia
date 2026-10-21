-- Prove2me | solution 1 for StatComplexityDM.LinearLB.rad_hellinger_bounds
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:08:56.610982+00:00
-- url     : https://prove2.me/submissions/86a036cd-a365-4e4f-b8be-e40a2b2b74dd

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_StatComplexityDM_LinearLB_Setting

set_option autoImplicit false
open FoundationsRL.GeneralDM StatComplexityDM.LinearLB

lemma RHB_sqrt_sq_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 ≤ (a - b) ^ 2 / (a + b) := by
  rcases eq_or_lt_of_le (add_nonneg ha hb) with h | h
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    subst ha0; subst hb0; simp
  · rw [le_div_iff₀ h]
    have hx := Real.sq_sqrt ha
    have hy := Real.sq_sqrt hb
    set x := Real.sqrt a
    set y := Real.sqrt b
    have hx0 : 0 ≤ x := Real.sqrt_nonneg _
    have hy0 : 0 ≤ y := Real.sqrt_nonneg _
    rw [← hx, ← hy]
    have : ((x ^ 2 - y ^ 2) ^ 2) = (x - y) ^ 2 * (x + y) ^ 2 := by ring
    rw [this]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    nlinarith [mul_nonneg hx0 hy0]

lemma RHB_hell_rad_le (μ₁ μ₂ : ℝ) (h1 : μ₁ ∈ Set.Icc (-1 : ℝ) 1) (h2 : μ₂ ∈ Set.Icc (-1 : ℝ) 1) :
    hellingerSq (rad μ₁) (rad μ₂) ≤
        (μ₁ - μ₂) ^ 2 / 2 * (1 / (2 + μ₁ + μ₂) + 1 / (2 - μ₁ - μ₂)) := by
  obtain ⟨a1, a2⟩ := h1
  obtain ⟨b1, b2⟩ := h2
  unfold hellingerSq rad
  rw [Fintype.sum_bool]
  simp only [if_true, Bool.false_eq_true, if_false]
  have e1 := RHB_sqrt_sq_le ((1 + μ₁) / 2) ((1 + μ₂) / 2) (by linarith) (by linarith)
  have e2 := RHB_sqrt_sq_le ((1 - μ₁) / 2) ((1 - μ₂) / 2) (by linarith) (by linarith)
  have k1 : ((1 + μ₁) / 2 - (1 + μ₂) / 2) ^ 2 / ((1 + μ₁) / 2 + (1 + μ₂) / 2)
      = (μ₁ - μ₂) ^ 2 / 2 * (1 / (2 + μ₁ + μ₂)) := by
    by_cases h : 2 + μ₁ + μ₂ = 0
    · have : (1 + μ₁) / 2 + (1 + μ₂) / 2 = 0 := by linarith
      rw [this, h]; simp
    · have h'' : (1 + μ₁) / 2 + (1 + μ₂) / 2 = (2 + μ₁ + μ₂) / 2 := by ring
      rw [h'']
      field_simp
      ring
  have k2 : ((1 - μ₁) / 2 - (1 - μ₂) / 2) ^ 2 / ((1 - μ₁) / 2 + (1 - μ₂) / 2)
      = (μ₁ - μ₂) ^ 2 / 2 * (1 / (2 - μ₁ - μ₂)) := by
    by_cases h : 2 - μ₁ - μ₂ = 0
    · have : (1 - μ₁) / 2 + (1 - μ₂) / 2 = 0 := by linarith
      rw [this, h]; simp
    · have h'' : (1 - μ₁) / 2 + (1 - μ₂) / 2 = (2 - μ₁ - μ₂) / 2 := by ring
      rw [h'']
      field_simp
      ring
  rw [mul_add]
  linarith

lemma RHB_hell_rad_zero (μ : ℝ) (h : μ ∈ Set.Icc (-1 : ℝ) 1) :
    hellingerSq (rad μ) (rad 0) ≤ 3 / 4 * μ ^ 2 := by
  obtain ⟨a1, a2⟩ := h
  unfold hellingerSq rad
  rw [Fintype.sum_bool]
  simp only [if_true, Bool.false_eq_true, if_false]
  have hx : Real.sqrt ((1 + μ) / 2) = Real.sqrt (1 + μ) / Real.sqrt 2 := Real.sqrt_div (by linarith) 2
  have hy : Real.sqrt ((1 - μ) / 2) = Real.sqrt (1 - μ) / Real.sqrt 2 := Real.sqrt_div (by linarith) 2
  have hz : Real.sqrt ((1 + 0) / 2) = 1 / Real.sqrt 2 := by
    rw [add_zero, Real.sqrt_div (by norm_num), Real.sqrt_one]
  have hz' : Real.sqrt ((1 - 0) / 2) = 1 / Real.sqrt 2 := by
    rw [sub_zero, Real.sqrt_div (by norm_num), Real.sqrt_one]
  rw [hx, hy, hz, hz']
  have s2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have s2p : 0 < Real.sqrt 2 := by positivity
  set x := Real.sqrt (1 + μ) with hxd
  set y := Real.sqrt (1 - μ) with hyd
  have hx2 : x ^ 2 = 1 + μ := Real.sq_sqrt (by linarith)
  have hy2 : y ^ 2 = 1 - μ := Real.sq_sqrt (by linarith)
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have expand : (x / Real.sqrt 2 - 1 / Real.sqrt 2) ^ 2 + (y / Real.sqrt 2 - 1 / Real.sqrt 2) ^ 2
      = ((x - 1) ^ 2 + (y - 1) ^ 2) / 2 := by
    field_simp
    rw [s2]
    ring
  rw [expand]
  -- need 2 - x - y ≤ 3/4 μ^2
  have hxy : (x * y) ^ 2 = 1 - μ ^ 2 := by rw [mul_pow, hx2, hy2]; ring
  set t := x * y with ht
  have ht0 : 0 ≤ t := mul_nonneg hx0 hy0
  have ht1 : t ≤ 1 := by nlinarith [sq_nonneg μ]
  have hs2 : (x + y) ^ 2 = 2 + 2 * t := by nlinarith
  have hs0 : 0 ≤ x + y := by linarith
  have key : (5 + 3 * t ^ 2) / 4 ≤ x + y := by
    apply abs_le_of_sq_le_sq' _ hs0 |>.2
    rw [hs2]
    nlinarith [mul_nonneg (sub_nonneg.2 ht1) (by positivity : (0:ℝ) ≤ 7 + 39 * t + 9 * t ^ 2 + 9 * t ^ 3)]
  nlinarith

theorem solution :
    (∀ μ₁ μ₂ : ℝ, μ₁ ∈ Set.Icc (-1 : ℝ) 1 → μ₂ ∈ Set.Icc (-1 : ℝ) 1 →
      hellingerSq (rad μ₁) (rad μ₂) ≤
        (μ₁ - μ₂) ^ 2 / 2 * (1 / (2 + μ₁ + μ₂) + 1 / (2 - μ₁ - μ₂))) ∧
    (∀ μ₁ μ₂ : ℝ, μ₁ ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2) → μ₂ ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2) →
      hellingerSq (rad μ₁) (rad μ₂) ≤ (μ₁ - μ₂) ^ 2) ∧
    (∀ μ : ℝ, μ ∈ Set.Icc (-1 : ℝ) 1 →
      hellingerSq (rad μ) (rad 0) ≤ 3 / 4 * μ ^ 2) := by
  refine ⟨RHB_hell_rad_le, ?_, RHB_hell_rad_zero⟩
  intro μ₁ μ₂ h1 h2
  obtain ⟨a1, a2⟩ := h1
  obtain ⟨b1, b2⟩ := h2
  have := RHB_hell_rad_le μ₁ μ₂ ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
  have i1 : 1 / (2 + μ₁ + μ₂) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have i2 : 1 / (2 - μ₁ - μ₂) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have : (μ₁ - μ₂) ^ 2 / 2 * (1 / (2 + μ₁ + μ₂) + 1 / (2 - μ₁ - μ₂)) ≤ (μ₁ - μ₂) ^ 2 / 2 * 2 :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith
