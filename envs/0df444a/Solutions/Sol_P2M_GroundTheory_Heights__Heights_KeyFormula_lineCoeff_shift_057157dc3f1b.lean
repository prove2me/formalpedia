-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KeyFormula_lineCoeff_shift_057157dc3f1b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:36.425097+00:00
-- url     : https://prove2.me/submissions/927663ae-eb34-4172-ac85-19dc8ee85d91

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
theorem _root_.solution (h : ℂ → ℂ) (n : ℕ) (C : ℂ)
    (h2 : ∀ w, h (w + I) = C * cexp (-2 * π * I * n * w) * h w) (k : ℤ) (y : ℝ) :
    lineCoeff h k (y + 1) = C * cexp (2 * π * k) * lineCoeff h (k + n) y := by
  unfold lineCoeff
  rw [← intervalIntegral.integral_const_mul]
  congr 1; funext x
  have e : (x : ℂ) + ((y + 1 : ℝ) : ℂ) * I = ((x : ℂ) + (y : ℂ) * I) + I := by push_cast; ring
  rw [e, h2]
  have : cexp (-2 * π * I * k * ((x + y * I) + I)) * cexp (-2 * π * I * n * (x + y * I)) =
      cexp (2 * π * k) * cexp (-2 * π * I * ((k + n : ℤ) : ℂ) * (x + y * I)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring_nf; rw [I_sq]; ring
  calc C * cexp (-2 * π * I * n * (x + y * I)) * h (x + y * I) *
        cexp (-2 * π * I * k * ((x + y * I) + I))
      = C * (cexp (-2 * π * I * k * ((x + y * I) + I)) * cexp (-2 * π * I * n * (x + y * I))) *
          h (x + y * I) := by ring
    _ = _ := by rw [this]; ring
end GroundTheory.Heights₂.Heights.KeyFormula
