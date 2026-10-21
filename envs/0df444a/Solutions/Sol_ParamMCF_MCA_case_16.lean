-- Prove2me | solution 1 for ParamMCF.MCA.case_16
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T23:50:23.632395+00:00
-- url     : https://prove2.me/submissions/4e6c28f3-db00-4bce-b0cb-cdf48d5a6cc3

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

theorem case_16_sol (g gt : ℝ → ℝ) (hg : IsMarginalCost g)
    (hgt : Continuous gt ∧ (∀ s, 0 < s → 0 ≤ gt s) ∧ (∀ s, s < 0 → gt s ≤ 0))
    (alpha beta m X : ℝ) (halpha : 1 < alpha) (hbeta : 0 ≤ beta) (hm : 0 < m) (hX : 0 < X)
    (hge : ∀ s ∈ Set.Icc (-X) X, |g s| ≤ |gt s|)
    (h16 : ∀ s ∈ Set.Icc (-X) X,
      |gt s - g s| ≤ (alpha - 1) * |g s| + beta / (m * X)) :
    ∀ x ∈ Set.Icc (-X) X,
      edgeCost g x ≤ edgeCost gt x ∧ edgeCost gt x ≤ alpha * edgeCost g x + beta / m := by
  intro x hx
  have hgc : Continuous g := hg.2.1.continuous
  set d := beta / (m * X) with hd
  have hd0 : 0 ≤ d := div_nonneg hbeta (by positivity)
  have hdX : X * d = beta / m := by rw [hd]; field_simp
  have hgt0 : gt 0 = 0 := le_antisymm (pmcf_nonpos_at_zero gt hgt.1.continuousAt hgt.2.2)
    (pmcf_nonneg_at_zero gt hgt.1.continuousAt hgt.2.1)
  have hcont : ∀ k e : ℝ, Continuous (fun s => k * g s + e) := fun k e =>
    (continuous_const.mul hgc).add continuous_const
  have hEg : edgeCost gt x = ∫ s in (0 : ℝ)..x, gt s := rfl
  have hEg' : edgeCost g x = ∫ s in (0 : ℝ)..x, g s := rfl
  rcases le_total 0 x with hx0 | hx0
  · have hpt : ∀ s ∈ Set.Icc 0 x, g s ≤ gt s ∧ gt s ≤ alpha * g s + d := by
      intro s hs
      have hsX : s ∈ Set.Icc (-X) X := ⟨by linarith [hs.1], hs.2.trans hx.2⟩
      have hgs := pmcf_g_nonneg g hg s hs.1
      have hgts : 0 ≤ gt s := by
        rcases eq_or_lt_of_le hs.1 with h | h
        · rw [← h, hgt0]
        · exact hgt.2.1 s h
      have h1 := hge s hsX
      have h2 := h16 s hsX
      rw [abs_of_nonneg hgs, abs_of_nonneg hgts] at h1
      rw [abs_of_nonneg hgs, abs_le] at h2
      constructor <;> nlinarith [h2.1, h2.2]
    have hl := pmcf_int_mono_pos _ _ hgc hgt.1 x hx0 (fun s hs => (hpt s hs).1)
    have hu := pmcf_int_mono_pos _ _ hgt.1 (hcont alpha d) x hx0 (fun s hs => (hpt s hs).2)
    rw [pmcf_int_affine g hgc] at hu
    rw [hEg, hEg']
    rw [← hEg'] at hl ⊢
    have : x * d ≤ X * d := mul_le_mul_of_nonneg_right hx.2 hd0
    constructor <;> nlinarith
  · have hpt : ∀ s ∈ Set.Icc x 0, alpha * g s + -d ≤ gt s ∧ gt s ≤ g s := by
      intro s hs
      have hsX : s ∈ Set.Icc (-X) X := ⟨hx.1.trans hs.1, by linarith [hs.2]⟩
      have hgs := pmcf_g_nonpos g hg s hs.2
      have hgts : gt s ≤ 0 := by
        rcases eq_or_lt_of_le hs.2 with h | h
        · rw [h, hgt0]
        · exact hgt.2.2 s h
      have h1 := hge s hsX
      have h2 := h16 s hsX
      rw [abs_of_nonpos hgs, abs_of_nonpos hgts] at h1
      rw [abs_of_nonpos hgs, abs_le] at h2
      constructor <;> nlinarith [h2.1, h2.2]
    have hl := pmcf_int_mono_neg _ _ hgt.1 hgc x hx0 (fun s hs => (hpt s hs).2)
    have hu := pmcf_int_mono_neg _ _ (hcont alpha (-d)) hgt.1 x hx0 (fun s hs => (hpt s hs).1)
    rw [pmcf_int_affine g hgc] at hu
    rw [hEg, hEg']
    rw [← hEg'] at hl ⊢
    have : -X * d ≤ x * d := mul_le_mul_of_nonneg_right hx.1 hd0
    constructor <;> nlinarith

end ParamMCF.MCA

open ParamMCF.MCA in
theorem solution (g gt : ℝ → ℝ) (hg : IsMarginalCost g)
    (hgt : Continuous gt ∧ (∀ s, 0 < s → 0 ≤ gt s) ∧ (∀ s, s < 0 → gt s ≤ 0))
    (alpha beta m X : ℝ) (halpha : 1 < alpha) (hbeta : 0 ≤ beta) (hm : 0 < m) (hX : 0 < X)
    (hge : ∀ s ∈ Set.Icc (-X) X, |g s| ≤ |gt s|)
    (h16 : ∀ s ∈ Set.Icc (-X) X,
      |gt s - g s| ≤ (alpha - 1) * |g s| + beta / (m * X)) :
    ∀ x ∈ Set.Icc (-X) X,
      edgeCost g x ≤ edgeCost gt x ∧ edgeCost gt x ≤ alpha * edgeCost g x + beta / m :=
  case_16_sol g gt hg hgt alpha beta m X halpha hbeta hm hX hge h16
