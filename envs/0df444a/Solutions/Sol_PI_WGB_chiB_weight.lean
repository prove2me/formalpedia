-- Prove2me | solution 1 for PI.WGB.chiB_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:34:02.943401+00:00
-- url     : https://prove2.me/submissions/e465d436-7f0e-4046-b7ab-8252285e69e9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFEqSumOfSubsetB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_RowActDiagMonomial
import Theorems.Thm_PI_WGB_chiB_add
import Theorems.Thm_PI_WGB_chiB_smul
import Theorems.Thm_PI_WGB_chiB_zero
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
theorem _root_.solution {n : ℕ} {σ : Type*} (t : Fin n → ℂ) (w : σ → (Fin n → ℕ)) (e : σ →₀ ℕ) :
    chiB t (Finsupp.weight w e) = ∏ v ∈ e.support, chiB t (w v) ^ e v := by
  rw [Finsupp.weight_apply, Finsupp.sum]
  induction e.support using Finset.cons_induction with
  | empty => simp [chiB_zero]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.prod_cons, chiB_add, chiB_smul, ih]
end PI.WGB
