-- Prove2me | solution 1 for PI.WGB.mkPtA_D
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:05:51.114791+00:00
-- url     : https://prove2.me/submissions/ebe01394-5080-4717-b508-686f52a7d9b7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_CoeffRowActDiagA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_StepACleared
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ProdMkPtA
import Theorems.Thm_PI_WGB_mStarA_cc
import Theorems.Thm_PI_WGB_mStarA_cl
import Theorems.Thm_PI_WGB_mStarA_lc
import Theorems.Thm_PI_WGB_mStarA_ll
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


attribute [local simp] PI.WGB.mStarA_cc
attribute [local simp] PI.WGB.mStarA_cl
attribute [local simp] PI.WGB.mStarA_lc
attribute [local simp] PI.WGB.mStarA_ll

set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
variable {n : ℕ}
namespace PI.WGB
theorem _root_.solution (dv : Fin n → ℂ) (z : Fin (n + 1) → ℂ) : IsDPtA (mkPtA dv z) := by
  intro a j ha hne
  obtain ⟨a', rfl⟩ : ∃ a' : Fin n, a = Fin.castSucc a' := ⟨⟨a.val, ha⟩, Fin.ext rfl⟩
  induction j using Fin.lastCases with
  | last => simp [mkPtA]
  | cast k =>
    simp only [mkPtA, Fin.lastCases_castSucc]
    rw [if_neg]
    rintro rfl
    exact hne rfl
end PI.WGB
