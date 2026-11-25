-- Prove2me | solution 1 for PI.SwBig.PhiDerivW.tv_deriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:34:25.02819+00:00
-- url     : https://prove2.me/submissions/d3c3f2f7-a692-47ac-a419-860c93c51700

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LongWeylElementSquare
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PhiDerivative_StarinvDeriv
import Theorems.Thm_PI_SwBig_PhiDerivW_starinv_deriv

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
variable (k r : ℕ)
namespace PI.SwBig.PhiDerivW
theorem _root_.solution : HasStrictFDerivAt (fun x : Fin r → ℂ => tv k r (1 + x)) (dvC k r) 0 := by
  rw [hasStrictFDerivAt_pi']
  intro i
  unfold dvC
  rw [ContinuousLinearMap.proj_pi]
  unfold tv
  by_cases h : i.val < r
  · simp only [h, ↓reduceDIte, Pi.add_apply, Pi.one_apply]
    exact (hasStrictFDerivAt_apply (𝕜 := ℝ) (i := (⟨i.val, h⟩ : Fin r)) (f := (0 : Fin r → ℂ))).const_add 1
  · by_cases h2 : i.val ≤ r + k
    · simp only [h, h2, ↓reduceDIte]
      exact hasStrictFDerivAt_const _ _
    · simp only [h, h2, ↓reduceDIte, Pi.add_apply, Pi.one_apply]
      have ha := hasStrictFDerivAt_apply (𝕜 := ℝ)
        (i := (⟨2 * r + k - i.val, by have := i.isLt; omega⟩ : Fin r)) (f := (0 : Fin r → ℂ))
      have hs : ∀ y : ℂ, y = 0 → HasStrictFDerivAt (fun z : ℂ => (star (1 + z))⁻¹)
          (-(Complex.conjCLE : ℂ →L[ℝ] ℂ)) y := by
        rintro y rfl; exact starinv_deriv
      refine ((hs _ (by simp)).comp 0 ha).congr_fderiv ?_
      refine ContinuousLinearMap.ext fun z => ?_
      simp
end PI.SwBig.PhiDerivW
