-- Prove2me | solution 1 for ParamMCF.MCA.eq_17
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T23:49:29.333233+00:00
-- url     : https://prove2.me/submissions/8d68d8dd-2c5a-4186-ab1b-465931b363b0

import Mathlib
import Definitions.Def_ParamMCF_MCA_Model

namespace ParamMCF.MCA

/-- A continuous function that is nonpositive on negatives is nonpositive at zero. -/
lemma pmcf_nonpos_at_zero (φ : ℝ → ℝ) (hφ : ContinuousAt φ 0) (h : ∀ s, s < 0 → φ s ≤ 0) :
    φ 0 ≤ 0 := by
  have ht : Filter.Tendsto φ (nhdsWithin 0 (Set.Iio 0)) (nhds (φ 0)) :=
    hφ.tendsto.mono_left nhdsWithin_le_nhds
  exact le_of_tendsto ht (eventually_nhdsWithin_of_forall fun s hs => h s hs)

/-- A continuous function that is nonnegative on positives is nonnegative at zero. -/
lemma pmcf_nonneg_at_zero (φ : ℝ → ℝ) (hφ : ContinuousAt φ 0) (h : ∀ s, 0 < s → 0 ≤ φ s) :
    0 ≤ φ 0 := by
  have ht : Filter.Tendsto φ (nhdsWithin 0 (Set.Ioi 0)) (nhds (φ 0)) :=
    hφ.tendsto.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun s hs => h s hs)

/-- A marginal cost vanishes at zero. -/
lemma pmcf_g_zero (g : ℝ → ℝ) (hg : IsMarginalCost g) : g 0 = 0 :=
  le_antisymm (pmcf_nonpos_at_zero g (hg.2.1.continuous.continuousAt) hg.2.2.2)
    (pmcf_nonneg_at_zero g (hg.2.1.continuous.continuousAt) hg.2.2.1)

lemma pmcf_g_nonneg (g : ℝ → ℝ) (hg : IsMarginalCost g) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ g x := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h, pmcf_g_zero g hg]
  · exact hg.2.2.1 x h

lemma pmcf_g_nonpos (g : ℝ → ℝ) (hg : IsMarginalCost g) (x : ℝ) (hx : x ≤ 0) : g x ≤ 0 := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [h, pmcf_g_zero g hg]
  · exact hg.2.2.2 x h

/-- Integral of an affine expression in `g`. -/
lemma pmcf_int_affine (g : ℝ → ℝ) (hg : Continuous g) (k d x : ℝ) :
    ∫ s in (0 : ℝ)..x, (k * g s + d) = k * edgeCost g x + x * d := by
  unfold edgeCost
  rw [intervalIntegral.integral_add ((hg.intervalIntegrable 0 x).const_mul k)
    intervalIntegrable_const, intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
  simp

/-- Monotonicity of `∫_0^x` for `x ≥ 0`. -/
lemma pmcf_int_mono_pos (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) (x : ℝ)
    (hx : 0 ≤ x) (h : ∀ s ∈ Set.Icc 0 x, u s ≤ v s) :
    ∫ s in (0 : ℝ)..x, u s ≤ ∫ s in (0 : ℝ)..x, v s :=
  intervalIntegral.integral_mono_on hx (hu.intervalIntegrable 0 x) (hv.intervalIntegrable 0 x) h

/-- Antitonicity of `∫_0^x` for `x ≤ 0`. -/
lemma pmcf_int_mono_neg (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) (x : ℝ)
    (hx : x ≤ 0) (h : ∀ s ∈ Set.Icc x 0, u s ≤ v s) :
    ∫ s in (0 : ℝ)..x, v s ≤ ∫ s in (0 : ℝ)..x, u s := by
  rw [intervalIntegral.integral_symm, intervalIntegral.integral_symm (a := x)]
  exact neg_le_neg
    (intervalIntegral.integral_mono_on hx (hu.intervalIntegrable x 0) (hv.intervalIntegrable x 0) h)

theorem eq_17_sol (g gt : ℝ → ℝ) (hg : IsMarginalCost g) (hgt : Continuous gt)
    (alpha beta m X : ℝ) (halpha : 1 < alpha) (hbeta : 0 ≤ beta) (hm : 0 < m) (hX : 0 < X)
    (h15 : ∀ s ∈ Set.Icc (-X) X,
      |gt s - g s| ≤ (alpha - 1) / (1 + alpha) * |g s| + beta / ((1 + alpha) * m * X)) :
    ∀ x ∈ Set.Icc (-X) X,
      2 / (1 + alpha) * edgeCost g x - beta / ((1 + alpha) * m) ≤ edgeCost gt x ∧
        edgeCost gt x ≤ 2 * alpha / (1 + alpha) * edgeCost g x + beta / ((1 + alpha) * m) := by
  intro x hx
  have hgc : Continuous g := hg.2.1.continuous
  have ha1 : 0 < 1 + alpha := by linarith
  set d := beta / ((1 + alpha) * m * X) with hd
  have hd0 : 0 ≤ d := div_nonneg hbeta (by positivity)
  have hdX : X * d = beta / ((1 + alpha) * m) := by
    rw [hd]; field_simp
  have hk1 : 2 / (1 + alpha) = 1 - (alpha - 1) / (1 + alpha) := by field_simp; ring
  have hk2 : 2 * alpha / (1 + alpha) = 1 + (alpha - 1) / (1 + alpha) := by field_simp; ring
  set c := (alpha - 1) / (1 + alpha) with hc
  have hcont : ∀ k e : ℝ, Continuous (fun s => k * g s + e) := fun k e =>
    (continuous_const.mul hgc).add continuous_const
  have hEg : edgeCost gt x = ∫ s in (0 : ℝ)..x, gt s := rfl
  rcases le_total 0 x with hx0 | hx0
  · -- `x ≥ 0`: on `[0, x]`, `g ≥ 0`
    have hpt : ∀ s ∈ Set.Icc 0 x, (1 - c) * g s + -d ≤ gt s ∧ gt s ≤ (1 + c) * g s + d := by
      intro s hs
      have hsX : s ∈ Set.Icc (-X) X := ⟨by linarith [hs.1], hs.2.trans hx.2⟩
      have h := h15 s hsX
      rw [abs_of_nonneg (pmcf_g_nonneg g hg s hs.1)] at h
      rw [abs_le] at h
      constructor <;> nlinarith [h.1, h.2]
    have hl := pmcf_int_mono_pos _ _ (hcont (1 - c) (-d)) hgt x hx0 (fun s hs => (hpt s hs).1)
    have hu := pmcf_int_mono_pos _ _ hgt (hcont (1 + c) d) x hx0 (fun s hs => (hpt s hs).2)
    rw [pmcf_int_affine g hgc] at hl hu
    rw [hEg, hk1, hk2]
    have : x * d ≤ X * d := mul_le_mul_of_nonneg_right hx.2 hd0
    constructor <;> nlinarith
  · -- `x ≤ 0`: on `[x, 0]`, `g ≤ 0`
    have hpt : ∀ s ∈ Set.Icc x 0, (1 + c) * g s + -d ≤ gt s ∧ gt s ≤ (1 - c) * g s + d := by
      intro s hs
      have hsX : s ∈ Set.Icc (-X) X := ⟨hx.1.trans hs.1, by linarith [hs.2]⟩
      have h := h15 s hsX
      rw [abs_of_nonpos (pmcf_g_nonpos g hg s hs.2)] at h
      rw [abs_le] at h
      constructor <;> nlinarith [h.1, h.2]
    have hl := pmcf_int_mono_neg _ _ (hcont (1 + c) (-d)) hgt x hx0 (fun s hs => (hpt s hs).1)
    have hu := pmcf_int_mono_neg _ _ hgt (hcont (1 - c) d) x hx0 (fun s hs => (hpt s hs).2)
    rw [pmcf_int_affine g hgc] at hl hu
    rw [hEg, hk1, hk2]
    have : -X * d ≤ x * d := mul_le_mul_of_nonneg_right hx.1 hd0
    constructor <;> nlinarith

end ParamMCF.MCA

open ParamMCF.MCA in
theorem solution (g gt : ℝ → ℝ) (hg : IsMarginalCost g) (hgt : Continuous gt)
    (alpha beta m X : ℝ) (halpha : 1 < alpha) (hbeta : 0 ≤ beta) (hm : 0 < m) (hX : 0 < X)
    (h15 : ∀ s ∈ Set.Icc (-X) X,
      |gt s - g s| ≤ (alpha - 1) / (1 + alpha) * |g s| + beta / ((1 + alpha) * m * X)) :
    ∀ x ∈ Set.Icc (-X) X,
      2 / (1 + alpha) * edgeCost g x - beta / ((1 + alpha) * m) ≤ edgeCost gt x ∧
        edgeCost gt x ≤ 2 * alpha / (1 + alpha) * edgeCost g x + beta / ((1 + alpha) * m) :=
  eq_17_sol g gt hg hgt alpha beta m X halpha hbeta hm hX h15
