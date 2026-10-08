-- Prove2me | solution 1 for TalagrandConc.QPoints.lemma_3_1_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T08:05:16.827499+00:00
-- url     : https://prove2.me/submissions/2a70a99d-2794-47d6-9854-207821d734ba

import Mathlib



namespace TalagrandConc.QPoints

open MeasureTheory

/-- `(q + 1 - q u) u^q ≤ 1` for `0 ≤ u ≤ 1`. -/
lemma key_poly_ineq (q : ℕ) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ((q : ℝ) + 1 - q * u) * u ^ q ≤ 1 := by
  set t := 1 - u with ht
  have hu : u = 1 - t := by rw [ht]; ring
  have ht0 : 0 ≤ t := by linarith
  have ht1 : t ≤ 1 := by linarith
  have hb : 1 + (q : ℝ) * t ≤ (1 + t) ^ q := one_add_mul_le_pow (by linarith) q
  have h1 : (q : ℝ) + 1 - q * u = 1 + q * t := by rw [hu]; ring
  rw [h1, hu]
  calc (1 + (q : ℝ) * t) * (1 - t) ^ q ≤ (1 + t) ^ q * (1 - t) ^ q :=
        mul_le_mul_of_nonneg_right hb (pow_nonneg (by linarith) q)
    _ = (1 - t ^ 2) ^ q := by rw [← mul_pow]; ring_nf
    _ ≤ 1 := pow_le_one₀ (by nlinarith) (by nlinarith)

theorem lemma_3_1_2_core {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : ℕ) (hq : 2 ≤ q) (g : Ω → ℝ) (hg : Measurable g)
    (hlow : ∀ ω, 1 / (q : ℝ) ≤ g ω) (hup : ∀ ω, g ω ≤ 1) :
    (∫ ω, 1 / g ω ∂μ) * (∫ ω, g ω ∂μ) ^ q ≤ 1 := by
  have hq0 : (0 : ℝ) < q := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hqinv : 0 < 1 / (q : ℝ) := by positivity
  have hgpos : ∀ ω, 0 < g ω := fun ω => lt_of_lt_of_le hqinv (hlow ω)
  have hint_g : Integrable g μ := by
    refine Integrable.of_bound hg.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hlow ω, hup ω]
  have hinv_le : ∀ ω, 1 / g ω ≤ q := by
    intro ω
    rw [div_le_iff₀ (hgpos ω)]
    have := hlow ω
    rw [div_le_iff₀ hq0] at this
    linarith
  have hint_inv : Integrable (fun ω => 1 / g ω) μ := by
    refine Integrable.of_bound (hg.inv.aestronglyMeasurable.congr ?_) q
      (Filter.Eventually.of_forall fun ω => ?_)
    · exact Filter.Eventually.of_forall fun ω => by simp
    · rw [Real.norm_eq_abs, abs_le]
      constructor
      · have := hinv_le ω; have : 0 < 1 / g ω := by have := hgpos ω; positivity
        linarith
      · exact hinv_le ω
  have hpt : ∀ ω, 1 / g ω ≤ ((q : ℝ) + 1) - q * g ω := by
    intro ω
    rw [div_le_iff₀ (hgpos ω)]
    have h1 := hlow ω
    rw [div_le_iff₀ hq0] at h1
    have h2 := hup ω
    nlinarith
  have h1 : ∫ ω, 1 / g ω ∂μ ≤ ∫ ω, (((q : ℝ) + 1) - q * g ω) ∂μ := by
    refine integral_mono hint_inv ?_ hpt
    exact (integrable_const _).sub (hint_g.const_mul _)
  have h2 : ∫ ω, (((q : ℝ) + 1) - q * g ω) ∂μ = ((q : ℝ) + 1) - q * ∫ ω, g ω ∂μ := by
    rw [integral_sub (integrable_const _) (hint_g.const_mul _), integral_const,
      integral_const_mul]
    simp
  have hu0 : 0 ≤ ∫ ω, g ω ∂μ := integral_nonneg fun ω => (hgpos ω).le
  have hu1 : ∫ ω, g ω ∂μ ≤ 1 := by
    have := integral_mono hint_g (integrable_const (1 : ℝ)) hup
    simpa using this
  have hA : 0 ≤ (∫ ω, g ω ∂μ) ^ q := pow_nonneg hu0 q
  calc (∫ ω, 1 / g ω ∂μ) * (∫ ω, g ω ∂μ) ^ q
      ≤ (((q : ℝ) + 1) - q * ∫ ω, g ω ∂μ) * (∫ ω, g ω ∂μ) ^ q := by
        rw [← h2]; exact mul_le_mul_of_nonneg_right h1 hA
    _ ≤ 1 := key_poly_ineq q _ hu0 hu1

end TalagrandConc.QPoints

open TalagrandConc.QPoints
open TalagrandConc.QPoints MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : ℕ) (hq : 2 ≤ q) (g : Ω → ℝ) (hg : Measurable g)
    (hlow : ∀ ω, 1 / (q : ℝ) ≤ g ω) (hup : ∀ ω, g ω ≤ 1) :
    (∫ ω, 1 / g ω ∂μ) * (∫ ω, g ω ∂μ) ^ q ≤ 1 := by
  exact lemma_3_1_2_core μ q hq g hg hlow hup
