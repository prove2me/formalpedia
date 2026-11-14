-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.hardcore_tilted_weight_law
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:43:31.565198+00:00
-- url     : https://prove2.me/submissions/c1f1df3f-dc95-442a-a7c6-b6ac151a6075

import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal

theorem solution (η : Measure ℝ) [IsProbabilityMeasure η] (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hb : ∀ᵐ h ∂η, -1 ≤ h ∧ h ≤ 1)
    (hint : Integrable (fun h : ℝ => h) η)
    (hmean : (∫ h : ℝ, h ∂η) = 0) :
    let tilt := η.withDensity (fun h : ℝ => ENNReal.ofReal (1 + θ*h))
    let ν := Measure.map (fun h : ℝ => (1-h)/(1+θ*h)) tilt
    IsProbabilityMeasure ν ∧
      (∀ᵐ w ∂ν, 0 ≤ w ∧ w ≤ 2/(1-θ)) ∧
      Integrable (fun w : ℝ => w) ν ∧ (∫ w : ℝ, w ∂ν) = 1 := by
  dsimp only
  let tilt := η.withDensity (fun h : ℝ => ENNReal.ofReal (1+θ*h))
  let W := fun h : ℝ => (1-h)/(1+θ*h)
  let ν := Measure.map W tilt
  have hdens : Measurable (fun h : ℝ => ENNReal.ofReal (1+θ*h)) := by fun_prop
  have hW : Measurable W := by dsimp [W]; fun_prop
  have hweight : ∀ᵐ h ∂η, 0 ≤ 1+θ*h := by
    filter_upwards [hb] with h hh
    nlinarith [mul_nonneg hθ (show 1+h ≥ 0 by linarith)]
  have hwi : Integrable (fun h : ℝ => 1+θ*h) η :=
    (integrable_const 1).add (hint.const_mul θ)
  have hwmean : (∫ h : ℝ, (1+θ*h) ∂η) = 1 := by
    rw [integral_add (integrable_const 1) (hint.const_mul θ), integral_const_mul]
    simp [hmean]
  have hprob : IsProbabilityMeasure tilt := by
    apply isProbabilityMeasure_iff.mpr
    dsimp [tilt]
    rw [withDensity_apply _ MeasurableSet.univ]
    simp only [Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal hwi hweight, hwmean]
    simp
  letI : IsProbabilityMeasure tilt := hprob
  have hν : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hW.aemeasurable
  have hboundη : ∀ᵐ h ∂η, 0 ≤ W h ∧ W h ≤ 2/(1-θ) := by
    filter_upwards [hb] with h hh
    have hd : 0 < 1+θ*h := by
      nlinarith [mul_nonneg hθ (show 1+h ≥ 0 by linarith)]
    have ht : 0 < 1-θ := by linarith
    have hn : 0 ≤ 1-h := by linarith
    refine ⟨div_nonneg hn hd.le, ?_⟩
    dsimp [W]
    apply (div_le_div_iff₀ hd ht).2
    nlinarith [mul_nonneg (show 1-h ≥ 0 by linarith) hθ,
      mul_nonneg hθ (show 1+h ≥ 0 by linarith)]
  have hboundtilt : ∀ᵐ h ∂tilt, 0 ≤ W h ∧ W h ≤ 2/(1-θ) :=
    (withDensity_absolutelyContinuous η _).ae_le hboundη
  have hboundν : ∀ᵐ w ∂ν, 0 ≤ w ∧ w ≤ 2/(1-θ) := by
    apply (ae_map_iff hW.aemeasurable ((measurableSet_le measurable_const measurable_id).inter
      (measurableSet_le measurable_id measurable_const))).2
    exact hboundtilt
  letI : IsProbabilityMeasure ν := hν
  have hνint : Integrable (fun w : ℝ => w) ν := by
    apply Integrable.of_bound measurable_id.aestronglyMeasurable (2/(1-θ))
    filter_upwards [hboundν] with w hw
    change ‖w‖ ≤ 2/(1-θ)
    rw [Real.norm_eq_abs, abs_of_nonneg hw.1]
    exact hw.2
  have hmeanν : (∫ w : ℝ, w ∂ν) = 1 := by
    dsimp [ν]
    change (∫ w, id w ∂Measure.map W tilt) = 1
    rw [integral_map hW.aemeasurable measurable_id.aestronglyMeasurable]
    dsimp only [Function.comp_def, id_eq]
    dsimp [tilt]
    rw [integral_withDensity_eq_integral_toReal_smul hdens (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    have heq : ∀ᵐ h ∂η, (ENNReal.ofReal (1+θ*h)).toReal • W h = 1-h := by
      filter_upwards [hb] with h hh
      have hd : 0 < 1+θ*h := by
        nlinarith [mul_nonneg hθ (show 1+h ≥ 0 by linarith)]
      rw [ENNReal.toReal_ofReal hd.le, smul_eq_mul]
      dsimp [W]
      field_simp
    rw [integral_congr_ae heq, integral_sub (integrable_const 1) hint]
    simp [hmean]
  exact ⟨hν,hboundν,hνint,hmeanν⟩
