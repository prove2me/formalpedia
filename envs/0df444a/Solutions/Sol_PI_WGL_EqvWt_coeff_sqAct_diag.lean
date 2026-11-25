-- Prove2me | solution 1 for PI.WGL.EqvWt.coeff_sqAct_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:33:50.656333+00:00
-- url     : https://prove2.me/submissions/622744a4-27a5-4de9-948d-9d10f2ab8496

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftEqvWt
import Theorems.Thm_PI_WGL_EqvWt_coeff_aeval_scale
import Theorems.Thm_PI_WGL_EqvWt_rowAct_diagonal
import Theorems.Thm_PI_WGL_EqvWt_prod_rowDeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
open PI.WGL.EqvWt
namespace PI.WGL.EqvWt
theorem _root_.solution {r : ℕ} (lam : DomWeight r) (t : Fin r → ℂˣ) (f : MvPolynomial (Fin r × Fin r) ℂ)
    (m : Fin r × Fin r →₀ ℕ) :
    coeff m (sqAct ℂ r lam (diagGL ℂ r t) f) =
      (∏ a, (t a : ℂ)) ^ lam.detShift * ((∏ a, (t a : ℂ) ^ rowDeg m a) * coeff m f) := by
  have hdet : detPow ℂ r (diagGL ℂ r t) lam.detShift = (∏ a, (t a : ℂ)) ^ lam.detShift := by
    unfold detPow
    rw [Units.val_zpow_eq_zpow_val]
    congr 1
    show Matrix.det (Matrix.diagonal fun a => (t a : ℂ)) = _
    exact Matrix.det_diagonal
  have htr : ((diagGL ℂ r t : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ).transpose =
      Matrix.diagonal fun a => (t a : ℂ) :=
    Matrix.diagonal_transpose _
  unfold sqAct
  rw [coeff_smul, smul_eq_mul, hdet, htr, rowAct_diagonal, coeff_aeval_scale,
    prod_rowDeg (fun a => (t a : ℂ)) m]
end PI.WGL.EqvWt
