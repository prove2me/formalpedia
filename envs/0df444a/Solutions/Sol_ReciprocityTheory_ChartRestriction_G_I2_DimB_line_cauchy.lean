-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.DimB.line_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:07:41.830484+00:00
-- url     : https://prove2.me/submissions/85072a24-103b-4cfc-8c2c-f39f9a0519c0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Complex
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.DimB
variable {k : ℕ}
attribute [local instance] ReciprocityTheory.ChartRestriction.G.I2.DimB._p2m_local_instance_697ec7c02f_11
attribute [local instance] ReciprocityTheory.ChartRestriction.G.I2.DimB._p2m_local_instance_697ec7c02f_13
attribute [local instance] ReciprocityTheory.ChartRestriction.G.I2.DimB._p2m_local_instance_697ec7c02f_16
namespace ReciprocityTheory.ChartRestriction.G.I2.DimB
theorem _root_.solution (Ψ : (Fin k → ℂ) → ℂ) (hd : Differentiable ℂ Ψ) (l : Fin k)
    (hp1 : ∀ z, Ψ (z + Pi.single l 1) = Ψ z) (u : Fin k → ℂ) (y : ℝ) :
    ∫ x in (0:ℝ)..1, Ψ (u + (x : ℂ) • Pi.single l 1) =
      ∫ x in (0:ℝ)..1, Ψ (u + ((y : ℂ) * I) • Pi.single l 1 + (x : ℂ) • Pi.single l 1) := by
  set f : ℂ → ℂ := fun c => Ψ (u + c • Pi.single l 1) with hf
  have hfd : Differentiable ℂ f :=
    hd.comp ((differentiable_const u).add (differentiable_id.smul_const _))
  have hper : ∀ c, f (c + 1) = f c := fun c => by
    simp only [hf, add_smul, one_smul, ← add_assoc, hp1]
  have H := integral_boundary_rect_eq_zero_of_differentiableOn f 0 (1 + y * I) hfd.differentiableOn
  have hre : (1 + (y : ℂ) * I).re = 1 := by simp
  have him : (1 + (y : ℂ) * I).im = y := by simp
  simp only [Complex.zero_re, Complex.zero_im, hre, him, Complex.ofReal_zero, zero_mul, add_zero,
    Complex.ofReal_one, zero_add] at H
  have h3 : (∫ t in (0:ℝ)..y, f (1 + (t : ℂ) * I)) = ∫ t in (0:ℝ)..y, f ((t : ℂ) * I) := by
    congr 1; funext t; rw [add_comm, hper]
  rw [h3] at H
  have H2 : (∫ x in (0:ℝ)..1, f (x : ℂ)) = ∫ x in (0:ℝ)..1, f ((x : ℂ) + y * I) := by
    linear_combination H
  have e1 : ∀ x : ℝ, u + ((y : ℂ) * I) • Pi.single l 1 + (x : ℂ) • Pi.single l 1 =
      u + ((x : ℂ) + y * I) • (Pi.single l 1 : Fin k → ℂ) := fun x => by
    rw [add_smul]; abel
  simp_rw [e1]
  exact H2
end ReciprocityTheory.ChartRestriction.G.I2.DimB
