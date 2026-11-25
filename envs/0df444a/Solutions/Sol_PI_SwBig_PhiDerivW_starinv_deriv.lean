-- Prove2me | solution 1 for PI.SwBig.PhiDerivW.starinv_deriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:28:30.902661+00:00
-- url     : https://prove2.me/submissions/2163e0d3-dcc2-4821-b592-f4e4e1b117b9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LongWeylElementSquare
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PhiDerivative_StarinvDeriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SwBig PI.SwBig.PhiDerivW
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra
namespace PI.SwBig.PhiDerivW
theorem _root_.solution :
    HasStrictFDerivAt (fun z : ℂ => (star (1 + z))⁻¹) (-(Complex.conjCLE : ℂ →L[ℝ] ℂ)) 0 := by
  have h1 : HasStrictFDerivAt (fun z : ℂ => 1 + (Complex.conjCLE : ℂ →L[ℝ] ℂ) z)
      (Complex.conjCLE : ℂ →L[ℝ] ℂ) 0 :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasStrictFDerivAt.const_add 1
  have h2 : ∀ y : ℂ, y = 1 → HasStrictFDerivAt (fun w : ℂ => w⁻¹)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (-((1 : ℂ) ^ 2)⁻¹)).restrictScalars ℝ) y := by
    rintro y rfl
    exact (hasStrictDerivAt_inv (𝕜 := ℂ) (x := 1) one_ne_zero).hasStrictFDerivAt.restrictScalars ℝ
  have h3 := (h2 _ (by simp)).comp 0 h1
  have hf : (fun z : ℂ => (star (1 + z))⁻¹) = (fun w : ℂ => w⁻¹) ∘
      (fun z : ℂ => 1 + (Complex.conjCLE : ℂ →L[ℝ] ℂ) z) := by
    funext z; simp [star_add]
  rw [hf]
  refine h3.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun z => ?_
  simp
end PI.SwBig.PhiDerivW
