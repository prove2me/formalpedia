-- Prove2me | solution 1 for PI.WGL.XiB.xi_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:41:13.493977+00:00
-- url     : https://prove2.me/submissions/90e63a72-544a-4b80-b1fb-e7a60c3ca757

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_RowsZStrictMono
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_EvalInitMinorNormLe
import Theorems.Thm_PI_WGL_XiB_sqAct_diag_xi
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
    (a : ℂˣ) :
    sqAct ℂ N lam (lastGL ℂ N a) (xi ℂ h lam sg) = ((a ^ degZ lam sg : ℂˣ) : ℂ) • xi ℂ h lam sg := by
  have hL : lastGL ℂ N a = diagGL ℂ N (fun b => if b.1 < n then 1 else a) := by
    apply Units.ext
    ext i j
    unfold lastGL diagGL
    simp [Matrix.diagonal_apply]
    split_ifs <;> simp_all <;> omega
  rw [hL, sqAct_diag_xi h lam sg hI]
  simp
end PI.WGL.XiB
