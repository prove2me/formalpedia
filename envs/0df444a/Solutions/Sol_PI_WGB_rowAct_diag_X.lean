-- Prove2me | solution 1 for PI.WGB.rowAct_diag_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:07:39.413591+00:00
-- url     : https://prove2.me/submissions/a361bd58-f275-45a6-9fa2-951e99c61086

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFEqSumOfSubsetB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_RowActDiagMonomial
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
open PI PI.WGB
open Formalism.BasicNotions MvPolynomial
namespace PI.WGB
theorem _root_.solution {N : ℕ} (d : Fin N → ℂ) (v : Fin N × Fin N) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) (Matrix.diagonal d) (X v) = C (d v.1) * X v := by
  simp only [Formalism.GradedWeylDivisibility.rowAct, aeval_X, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single v.1]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp
end PI.WGB
