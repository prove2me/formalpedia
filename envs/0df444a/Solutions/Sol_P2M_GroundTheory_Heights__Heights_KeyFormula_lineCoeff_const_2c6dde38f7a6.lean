-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KeyFormula_lineCoeff_const_2c6dde38f7a6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:35.371772+00:00
-- url     : https://prove2.me/submissions/2f7f06a4-7c51-4f53-b7f0-9758595ada60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_RigSymFormTauINontrivial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_ThetaThreeFamLinearIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.KeyFormula
open Complex Real MeasureTheory intervalIntegral Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.KeyFormula
theorem _root_.solution (h : ℂ → ℂ) (hd : Differentiable ℂ h) (h1 : ∀ w, h (w + 1) = h w)
    (k : ℤ) (y₁ y₂ : ℝ) : lineCoeff h k y₁ = lineCoeff h k y₂ := by
  set F : ℂ → ℂ := fun w => h w * cexp (-2 * π * I * k * w) with hF
  have hFd : Differentiable ℂ F := hd.mul (by fun_prop)
  have hper : ∀ w, F (w + 1) = F w := by
    intro w
    simp only [hF, h1]
    congr 1
    rw [Complex.exp_eq_exp_iff_exists_int]
    exact ⟨-k, by push_cast; ring⟩
  have := integral_boundary_rect_eq_zero_of_differentiableOn F ⟨0, y₁⟩ ⟨1, y₂⟩ hFd.differentiableOn
  simp only at this
  have hv : (∫ y : ℝ in y₁..y₂, F ((1 : ℝ) + y * I)) = ∫ y : ℝ in y₁..y₂, F ((0 : ℝ) + y * I) := by
    congr 1; funext y
    rw [show ((1 : ℝ) : ℂ) + y * I = ((0 : ℝ) + y * I) + 1 by push_cast; ring, hper]
  rw [hv, add_sub_cancel_right, sub_eq_zero] at this
  simpa [lineCoeff, hF] using this
end GroundTheory.Heights₂.Heights.KeyFormula
