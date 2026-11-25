-- Prove2me | solution 1 for PI.WGL.EqvWt.rowAct_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:07:19.721869+00:00
-- url     : https://prove2.me/submissions/e5f197ea-be32-409c-8196-195b180774b0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftEqvWt
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
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
open PI.WGL.EqvWt
namespace PI.WGL.EqvWt
theorem _root_.solution {r c : ℕ} (d : Fin r → ℂ) :
    rowAct ℂ (n := c) (Matrix.diagonal d) = aeval (fun v : Fin r × Fin c => C (d v.1) * X v) := by
  unfold Formalism.GradedWeylDivisibility.rowAct
  congr 1
  funext v
  rw [Finset.sum_eq_single v.1]
  · simp
  · intro b _ hb
    simp [Matrix.diagonal_apply_ne _ (Ne.symm hb)]
  · simp
end PI.WGL.EqvWt
