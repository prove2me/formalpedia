-- Prove2me | solution 2 for SpherePacking.Alternative.fourierReal_schwartzDilation_apply
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:52:19.364458+00:00
-- url     : https://prove2.me/submissions/ed6d79ef-4c1d-4f6c-a0d0-f9e63e159e5f

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
theorem h47_dil {d : ℕ} (f : Schwartz d) (a : ℝ) (ha : 0 < a) (ξ : Ambient d) :
    fourierReal (schwartzDilation a ha.ne' f) ξ = (a ^ d)⁻¹ * fourierReal f (a⁻¹ • ξ) := by
  unfold fourierReal
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, Real.fourier_eq, Real.fourier_eq]
  have hdil : ∀ v : Ambient d, (schwartzDilation a ha.ne' f) v = f (a • v) := fun v => rfl
  simp_rw [hdil]
  let G : Ambient d → ℂ := fun y => 𝐞 (-inner ℝ (a⁻¹ • y) ξ) • f y
  have hG : ∀ v : Ambient d, 𝐞 (-inner ℝ v ξ) • f (a • v) = G (a • v) := by
    intro v; simp only [G, inv_smul_smul₀ ha.ne']
  simp_rw [hG]
  rw [MeasureTheory.Measure.integral_comp_smul MeasureTheory.volume G a, finrank_euclideanSpace_fin]
  have hG2 : ∀ y : Ambient d, G y = 𝐞 (-inner ℝ y (a⁻¹ • ξ)) • f y := by
    intro y; simp only [G, real_inner_smul_left, real_inner_smul_right]
  simp_rw [hG2]
  rw [abs_of_pos (inv_pos.2 (pow_pos ha d)), Complex.real_smul, Complex.re_ofReal_mul]

theorem solution {d : ℕ} (a : ℝ) (ha : 0 < a)
    (f : Schwartz d) (ξ : Ambient d) :
    fourierReal (schwartzDilation a ha.ne' f) ξ =
      (a ^ d)⁻¹ * fourierReal f (a⁻¹ • ξ) := by
  exact h47_dil f a ha ξ

