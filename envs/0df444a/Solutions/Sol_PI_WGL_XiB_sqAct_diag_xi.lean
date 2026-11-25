-- Prove2me | solution 1 for PI.WGL.XiB.sqAct_diag_xi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:16:29.612986+00:00
-- url     : https://prove2.me/submissions/15bd57ee-7634-4334-8a9d-0efb67688de2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_RowsZStrictMono
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_EvalInitMinorNormLe
import Theorems.Thm_PI_WGL_XiB_diag_scalar
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_WGL_XiA_rowAct_xi
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
    (s : Fin N → ℂˣ) :
    sqAct ℂ N lam (diagGL ℂ N s) (xi ℂ h lam sg) =
      (((∏ j : Fin n, s ⟨j.1, by omega⟩ ^ sg.w j) * s ⟨n, by omega⟩ ^ degZ lam sg : ℂˣ) : ℂ) • xi ℂ h lam sg := by
  have hG : XiA.GoodG n h (Matrix.diagonal fun a => (s a : ℂ)) := by
    unfold XiA.GoodG
    refine ⟨fun a b hab => ?_, fun b hb => ?_⟩
    · exact Matrix.diagonal_apply_ne _ (ne_of_lt hab).symm
    · apply Matrix.diagonal_apply_ne
      intro e
      apply hb
      rw [e]
  have hcoe : ((diagGL ℂ N s : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      Matrix.diagonal fun a => (s a : ℂ) := by
    ext i j
    unfold diagGL
    simp [Matrix.diagonal_apply]
  unfold sqAct
  rw [hcoe, XiA.rowAct_xi h lam sg _ hG, MvPolynomial.C_mul', smul_smul, diag_scalar h lam sg hI s]
end PI.WGL.XiB
