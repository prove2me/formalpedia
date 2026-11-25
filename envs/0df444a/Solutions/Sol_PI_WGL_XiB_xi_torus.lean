-- Prove2me | solution 1 for PI.WGL.XiB.xi_torus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:41:16.696262+00:00
-- url     : https://prove2.me/submissions/e0304899-1593-43f5-b8e6-c5d7ab931ace

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_RowsZStrictMono
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_EvalInitMinorNormLe
import Theorems.Thm_PI_WGL_XiB_sqAct_diag_xi
import Theorems.Thm_PI_WGL_XiB_embGL_diag
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.XiB
open Formalism.BasicNotions MvPolynomial
namespace PI.WGL.XiB
theorem _root_.solution {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg)
    (t : Fin n → ℂˣ) :
    sqAct ℂ N lam (embGL ℂ n N h (diagGL ℂ n t)) (xi ℂ h lam sg) =
      ((∏ j, t j ^ sg.w j : ℂˣ) : ℂ) • xi ℂ h lam sg := by
  rw [embGL_diag, sqAct_diag_xi h lam sg hI]
  simp
end PI.WGL.XiB
