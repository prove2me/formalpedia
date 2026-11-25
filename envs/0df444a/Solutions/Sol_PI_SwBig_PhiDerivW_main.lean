-- Prove2me | solution 1 for PI.SwBig.PhiDerivW.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:39:14.389989+00:00
-- url     : https://prove2.me/submissions/3e96f5d8-da50-404c-9d0f-71d716aad576

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LongWeylElementSquare
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PhiDerivative_StarinvDeriv
import Theorems.Thm_PI_SwBig_PhiDerivW_dvC_apply
import Theorems.Thm_PI_SwBig_PhiDerivW_tv_deriv
import Theorems.Thm_PI_SwBig_PhiDerivW_diagC_apply
import Theorems.Thm_PI_SwBig_PhiDerivW_tv_one
import Theorems.Thm_PI_SwBig_PhiDerivW_diag1

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
theorem _root_.solution (hW : LongWeylElementSquare) :
    HasStrictFDerivAt
      (fun p : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r => Phi k r p.1 p.2.1 p.2.2.1 p.2.2.2)
      (Lm k r) 0 := by
  have e0 : ∀ y : Mat k r, y = 0 →
      HasStrictFDerivAt (NormedSpace.exp : Mat k r → Mat k r) (1 : Mat k r →L[ℝ] Mat k r) y := by
    rintro y rfl; exact hasStrictFDerivAt_exp_zero
  have c0 : ∀ (f : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r → Mat k r) f',
      HasStrictFDerivAt f f' 0 → f 0 = 0 →
      HasStrictFDerivAt (fun p => NormedSpace.exp (f p)) ((1 : Mat k r →L[ℝ] Mat k r).comp f') 0 :=
    fun f f' hf h0 => (e0 _ h0).comp 0 hf
  have hX := c0 _ _ (hasStrictFDerivAt_fst (𝕜 := ℝ)
    (p := (0 : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r))) (by simp)
  have hZ := c0 _ _ (hasStrictFDerivAt_snd (𝕜 := ℝ)
    (p := (0 : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r))).snd.fst (by simp)
  have hX' := c0 _ _ (hasStrictFDerivAt_snd (𝕜 := ℝ)
    (p := (0 : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r))).snd.snd.neg (by simp)
  have hT := (diagC k r).hasStrictFDerivAt.comp 0 ((tv_deriv k r).comp 0
    (hasStrictFDerivAt_snd (𝕜 := ℝ) (p := (0 : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r))).fst)
  have h1 := (hX.const_mul (w0B k r)).mul_const' (w0B k r)
  have h5 := ((h1.mul' hT).mul' hZ).mul' hX'
  apply h5.congr_fderiv
  refine ContinuousLinearMap.ext fun p => ?_
  simp only [Pi.mul_apply, Prod.fst_zero, Prod.snd_zero, NormedSpace.exp_zero, mul_one, hW k r,
    add_zero, neg_zero, Pi.neg_apply, diagC_apply, tv_one]
  change (1 * diagonal 1) * (-p.2.2.2) + ((1 * diagonal 1) * p.2.2.1 +
      (1 * diagC k r (dvC k r p.2.1) + w0B k r * p.1 * w0B k r * diagonal 1) * 1) * 1 =
    w0B k r * p.1 * w0B k r + diagonal (dv k r p.2.1) + p.2.2.1 - p.2.2.2
  rw [diagC_apply, dvC_apply, diag1]
  simp only [one_mul, mul_one]
  abel
end PI.SwBig.PhiDerivW
