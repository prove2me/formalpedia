-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P50.misclassification_variance_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:01:43.610366+00:00
-- url     : https://prove2.me/submissions/33da8638-53ab-4e2d-9b56-3f93166aca77

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P50

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open QAlgorithms.Papers.Independent.Advance50.P50

theorem s110_cantelli {Omega : Type*} [MeasurableSpace Omega]
    (mu0 : Measure Omega) [IsProbabilityMeasure mu0]
    (X : Omega → ℝ) (hL2 : MemLp X 2 mu0) (delta : ℝ) (hd : 0 < delta) :
    (mu0 {w | delta ≤ (∫ z, X z ∂mu0) - X w}).toReal ≤
      variance X mu0 / (variance X mu0 + delta ^ 2) := by
  set m := ∫ z, X z ∂mu0 with hm
  set V := variance X mu0 with hV
  have hV0 : 0 ≤ V := variance_nonneg X mu0
  set t := V / delta with ht
  have ht0 : 0 ≤ t := div_nonneg hV0 hd.le
  have hXi : Integrable X mu0 := hL2.integrable one_le_two
  have hsq : Integrable (fun w => (X w - m) ^ 2) mu0 :=
    (hL2.sub (memLp_const m)).integrable_sq
  have hlin : Integrable (fun w => X w - m) mu0 := hXi.sub (integrable_const m)
  have hf : Integrable (fun w => (m - X w + t) ^ 2) mu0 := by
    have : (fun w => (m - X w + t) ^ 2) = fun w => (X w - m) ^ 2 + (-(2 * t)) * (X w - m) + t ^ 2 := by
      funext w; ring
    rw [this]
    exact (hsq.add (hlin.const_mul _)).add (integrable_const _)
  have hint : ∫ w, (m - X w + t) ^ 2 ∂mu0 = V + t ^ 2 := by
    have : (fun w => (m - X w + t) ^ 2) = fun w => (X w - m) ^ 2 + (-(2 * t)) * (X w - m) + t ^ 2 := by
      funext w; ring
    have hA : Integrable (fun w => (X w - m) ^ 2 + (-(2 * t)) * (X w - m)) mu0 :=
      hsq.add (hlin.const_mul _)
    have hB : Integrable (fun w => (-(2 * t)) * (X w - m)) mu0 := hlin.const_mul _
    rw [this, integral_add hA (integrable_const _), integral_add hsq hB, integral_const_mul,
      integral_sub hXi (integrable_const m), hV, variance_eq_integral hL2.1.aemeasurable]
    simp [hm]
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := mu0) (Filter.Eventually.of_forall fun w => sq_nonneg (m - X w + t)) hf ((delta + t) ^ 2)
  rw [hint] at hmk
  have hsub : mu0.real {w | delta ≤ m - X w} ≤ mu0.real {w | (delta + t) ^ 2 ≤ (m - X w + t) ^ 2} := by
    apply measureReal_mono _ (measure_ne_top _ _)
    intro w hw
    simp only [Set.mem_setOf_eq] at hw ⊢
    have : 0 ≤ delta + t := by linarith
    nlinarith
  have hpos : 0 < (delta + t) ^ 2 := by positivity
  have hP : mu0.real {w | delta ≤ m - X w} ≤ (V + t ^ 2) / (delta + t) ^ 2 := by
    rw [le_div_iff₀ hpos]; nlinarith
  have heq : (V + t ^ 2) / (delta + t) ^ 2 = V / (V + delta ^ 2) := by
    rw [ht]
    have : V + delta ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  rw [← heq]
  exact hP

theorem solution {Omega : Type*} [MeasurableSpace Omega]
    (mu0 mu1 : Measure Omega) [IsProbabilityMeasure mu0] [IsProbabilityMeasure mu1]
    (X : Omega → ℝ) (hX : Measurable X) (hL2 : MemLp X 2 mu0)
    (c b1 b2 : ℝ) (hclass1 : ∀ᵐ w ∂mu1, X w = c)
    (hclass0 : ∀ᵐ w ∂mu0, X w ∈ Set.Icc b1 b2)
    (hmean : c < ∫ w, X w ∂mu0) :
    let delta := (∫ w, X w ∂mu0) - c
    posteriorAt mu0 mu1 X c ≤ (mu0 {w | X w = c}).toReal ∧
    (mu0 {w | X w = c}).toReal ≤
      (mu0 {w | delta ≤ (∫ z, X z ∂mu0) - X w}).toReal ∧
    (mu0 {w | delta ≤ (∫ z, X z ∂mu0) - X w}).toReal ≤
      variance X mu0 / (variance X mu0 + delta ^ 2) := by
  intro delta
  have hmeas : MeasurableSet {w | X w = c} := hX (measurableSet_singleton c)
  have h1 : mu1 {w | X w = c} = 1 := by
    rw [← prob_compl_eq_zero_iff hmeas]
    rw [ae_iff] at hclass1
    simpa [Set.compl_def] using hclass1
  refine ⟨?_, ?_, s110_cantelli mu0 X hL2 delta (by simp only [delta]; linarith)⟩
  · unfold posteriorAt
    rw [h1, ENNReal.toReal_one]
    have ha : 0 ≤ (mu0 {w | X w = c}).toReal := ENNReal.toReal_nonneg
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  · apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    intro w hw
    simp only [Set.mem_setOf_eq] at hw ⊢
    simp only [delta, hw]; exact le_refl _
