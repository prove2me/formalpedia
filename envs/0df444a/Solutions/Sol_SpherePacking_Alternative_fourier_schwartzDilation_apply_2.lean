-- Prove2me | solution 2 for SpherePacking.Alternative.fourier_schwartzDilation_apply
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:48:26.457767+00:00
-- url     : https://prove2.me/submissions/3d49ffde-1753-4d36-ba96-2a02ad2d6a99

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory
open scoped FourierTransform Real Topology
open SpherePacking SpherePacking.Alternative


theorem solution {d : ℕ} (a : ℝ) (ha : 0 < a)
    (f : Schwartz d) (ξ : Ambient d) :
    (𝓕 (schwartzDilation a ha.ne' f) : Schwartz d) ξ =
      (a ^ d)⁻¹ • (𝓕 f : Schwartz d) (a⁻¹ • ξ) := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, Real.fourier_eq, Real.fourier_eq]
  have h := MeasureTheory.Measure.integral_comp_smul_of_nonneg (μ := (volume : Measure (Ambient d)))
    (fun y : Ambient d => Real.fourierChar (-inner ℝ y (a⁻¹ • ξ)) • f y) a (hR := ha.le)
  rw [finrank_euclideanSpace_fin] at h
  rw [← h]
  congr 1
  funext x
  have hx : inner ℝ (a • x) (a⁻¹ • ξ) = inner ℝ x ξ := by
    rw [inner_smul_left, inner_smul_right]
    simp only [RCLike.conj_to_real]
    field_simp
  simp only [hx]
  rfl

