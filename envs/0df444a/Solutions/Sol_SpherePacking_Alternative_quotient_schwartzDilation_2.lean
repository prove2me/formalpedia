-- Prove2me | solution 2 for SpherePacking.Alternative.quotient_schwartzDilation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:17:00.99796+00:00
-- url     : https://prove2.me/submissions/c2ae6b6b-6f22-4309-9a56-e7901efc228a

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
    (f : Schwartz d) :
    quotient (schwartzDilation a ha.ne' f) =
      a ^ d * quotient f := by
  have hF0 : ∀ g : Schwartz d, (𝓕 g : Schwartz d) 0 = ∫ x, g x := by
    intro g
    calc (𝓕 g : Schwartz d) 0 = (𝓕 (g : Ambient d → ℂ)) 0 := congrFun (SchwartzMap.fourier_coe g) 0
      _ = ∫ x, g x := by rw [Real.fourier_eq]; simp
  have happ : ∀ x, schwartzDilation a ha.ne' f x = f (a • x) := fun x => rfl
  unfold quotient fourierReal
  rw [hF0, hF0, happ, smul_zero]
  simp_rw [happ]
  rw [MeasureTheory.Measure.integral_comp_smul_of_nonneg volume (fun x => f x) a (hR := ha.le),
    finrank_euclideanSpace_fin, Complex.smul_re, smul_eq_mul]
  rw [mul_comm ((a ^ d)⁻¹), ← div_div, div_inv_eq_mul]
  ring

