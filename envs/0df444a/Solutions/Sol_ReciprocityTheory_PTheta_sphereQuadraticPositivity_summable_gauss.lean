-- Prove2me | solution 1 for ReciprocityTheory.PTheta.sphereQuadraticPositivity.summable_gauss
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:46:14.677077+00:00
-- url     : https://prove2.me/submissions/3a4e79a8-0a8d-4e49-9ea5-e2e9c8bf8d6e

import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_NormInvSmulMemSphere

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix
open ReciprocityTheory ReciprocityTheory.PTheta ReciprocityTheory.PTheta.sphereQuadraticPositivity
variable {ι : Type*} [Fintype ι]
namespace ReciprocityTheory.PTheta.sphereQuadraticPositivity
theorem _root_.solution (β C : ℝ) (hβ : 0 < β) :
    Summable (fun k : ℤ => Real.exp (-(β / 4) * (k : ℝ) ^ 2 + C)) := by
  have hτ : 0 < (⟨0, β / (4 * Real.pi)⟩ : ℂ).im := by
    show 0 < β / (4 * Real.pi)
    positivity
  have hs := ((summable_jacobiTheta₂_term_iff 0 _).mpr hτ).norm
  have key : (fun k : ℤ => Real.exp (-(β / 4) * (k : ℝ) ^ 2 + C)) = fun k : ℤ =>
      Real.exp C * ‖jacobiTheta₂_term k 0 (⟨0, β / (4 * Real.pi)⟩ : ℂ)‖ := by
    funext k
    rw [norm_jacobiTheta₂_term, ← Real.exp_add]
    congr 1
    dsimp only
    simp only [Complex.zero_im, mul_zero, sub_zero]
    field_simp
    ring
  rw [key]
  exact hs.mul_left _
end ReciprocityTheory.PTheta.sphereQuadraticPositivity
