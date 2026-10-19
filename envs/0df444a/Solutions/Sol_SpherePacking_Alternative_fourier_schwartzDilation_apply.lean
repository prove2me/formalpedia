-- Prove2me | solution 1 for SpherePacking.Alternative.fourier_schwartzDilation_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:38.10986+00:00
-- url     : https://prove2.me/submissions/3fd3afa5-e217-45fc-b342-657ed94f0ecb

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_SpherePacking_Alternative_schwartzDilation_apply
import Theorems.Thm_SpherePacking_Alternative_schwartzDilation_zero
attribute [local simp] SpherePacking.Alternative.schwartzDilation_apply
attribute [local simp] SpherePacking.Alternative.schwartzDilation_zero

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
namespace SpherePacking.Alternative
theorem _root_.solution {d : ℕ} (a : ℝ) (ha : 0 < a)
    (f : Schwartz d) (ξ : Ambient d) :
    (𝓕 (schwartzDilation a ha.ne' f) : Schwartz d) ξ =
      (a ^ d)⁻¹ • (𝓕 f : Schwartz d) (a⁻¹ • ξ) := by
  change 𝓕 (schwartzDilation a ha.ne' f : Ambient d → ℂ) ξ =
    (a ^ d)⁻¹ • 𝓕 (f : Ambient d → ℂ) (a⁻¹ • ξ)
  rw [Real.fourier_eq', Real.fourier_eq']
  let g : Ambient d → ℂ := fun y ↦
    Complex.exp ((↑(-2 * Real.pi * @inner ℝ _ _ y (a⁻¹ • ξ)) : ℂ) *
      Complex.I) • f y
  have hinner (y : Ambient d) :
      @inner ℝ _ _ (a • y) (a⁻¹ • ξ) = @inner ℝ _ _ y ξ := by
    rw [real_inner_smul_left, real_inner_smul_right]
    field_simp
  calc
    (∫ y : Ambient d,
      Complex.exp ((↑(-2 * Real.pi * @inner ℝ _ _ y ξ) : ℂ) *
        Complex.I) • schwartzDilation a ha.ne' f y) =
        ∫ y : Ambient d, g (a • y) := by
          apply integral_congr_ae
          filter_upwards with y
          simp [g, schwartzDilation_apply, hinner y]
    _ = (a ^ d)⁻¹ • ∫ y : Ambient d, g y := by
          simpa [finrank_euclideanSpace] using
            (Measure.integral_comp_smul_of_nonneg
              (volume : Measure (Ambient d)) g a (hR := ha.le))
    _ = (a ^ d)⁻¹ •
        ∫ y : Ambient d,
          Complex.exp
            ((↑(-2 * Real.pi * @inner ℝ _ _ y (a⁻¹ • ξ)) : ℂ) *
              Complex.I) • f y := by
          rfl
end SpherePacking.Alternative
