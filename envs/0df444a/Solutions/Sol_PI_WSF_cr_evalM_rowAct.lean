-- Prove2me | solution 1 for PI.WSF.cr_evalM_rowAct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:27:22.229923+00:00
-- url     : https://prove2.me/submissions/cadcd363-386d-42ca-a57a-bbf0e826cac9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_InstMeasurableSpaceMat
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_CrRowActRowAct
import Theorems.Thm_PI_WSF_cr_rowAct_X
import Theorems.Thm_PI_WSF_cr_rowAct_C
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
open PI PI.WSF
open Formalism.BasicNotions MvPolynomial
namespace PI.WSF
theorem _root_.solution {N : ℕ} (g x : Matrix (Fin N) (Fin N) ℂ) (s : MvPolynomial (Fin N × Fin N) ℂ) :
    evalM x (Formalism.GradedWeylDivisibility.rowAct ℂ g s) = evalM (g * x) s := by
  induction s using MvPolynomial.induction_on
  next a =>
    rw [cr_rowAct_C]
    simp [evalM]
  next p q hp hq =>
    simp only [map_add, evalM] at hp hq ⊢
    rw [hp, hq]
  next p v hp =>
    simp only [evalM, map_mul] at hp ⊢
    rw [hp, cr_rowAct_X]
    congr 1
    simp [Matrix.mul_apply]
end PI.WSF
