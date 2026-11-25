-- Prove2me | solution 1 for PI.WGB.sqAct_oneC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:14:18.959192+00:00
-- url     : https://prove2.me/submissions/5db2cc48-af24-4502-a887-5347fb6036e1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_AevalScaleMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_TransposeConjComm
import Theorems.Thm_PI_WGB_sqAct_eq
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_WGB_rowAct_one_apply
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
open PI PI.WGB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
open Formalism.REAL (fockF)
namespace PI.WGB
theorem _root_.solution {N : ℕ} (lam : DomWeight N) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    sqAct ℂ N lam 1 f = f := by
  simp [sqAct_eq, rowAct_one_apply]
end PI.WGB
