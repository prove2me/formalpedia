-- Prove2me | solution 1 for TwoAssumptions.prop8_volume_invariant
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:29:53.900195+00:00
-- url     : https://prove2.me/submissions/c8368583-134a-4cb1-87e5-1cbdcb127634

import Mathlib
open scoped ContDiff
namespace TwoAssumptions

theorem _root_.solution (m : ℕ)
    (f : (Fin m → ℝ) → (Fin m → ℝ))
    (hf : ContDiff ℝ 1 f) (hbij : Function.Bijective f)
    (hJ : ∀ x, |(fderiv ℝ f x).det| = 1) :
    MeasureTheory.MeasurePreserving f MeasureTheory.volume MeasureTheory.volume := by
  have hmeas : Measurable f := hf.continuous.measurable
  refine ⟨hmeas, ?_⟩
  ext A hA
  rw [MeasureTheory.Measure.map_apply hmeas hA]
  have hs : MeasurableSet (f ⁻¹' A) := hmeas hA
  have hder : ∀ x ∈ f ⁻¹' A, HasFDerivWithinAt f (fderiv ℝ f x) (f ⁻¹' A) x := fun x _ =>
    ((hf.differentiable (by norm_num)) x).hasFDerivAt.hasFDerivWithinAt
  have h := MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image MeasureTheory.volume hs hder hbij.injective.injOn
  rw [Set.image_preimage_eq A hbij.surjective] at h
  rw [← h]
  simp [hJ]


end TwoAssumptions
