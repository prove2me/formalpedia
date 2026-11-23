-- Prove2me | solution 1 for PI.WGB.mStarA_ll
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:29:50.549362+00:00
-- url     : https://prove2.me/submissions/abafb56c-85a2-4e46-9728-944c129bf984

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_CoeffRowActDiagA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_StepACleared
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ProdMkPtA
import Theorems.Thm_PI_WGB_mStarA_cc
import Theorems.Thm_PI_WGB_mStarA_cl
import Theorems.Thm_PI_WGB_mStarA_lc
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

set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
variable {n : ℕ}
namespace PI.WGB
theorem _root_.solution (kap : Fin n → ℕ) (ν : Fin (n + 1) → ℕ) :
    mStarA kap ν (Fin.last n, Fin.last n) = ν (Fin.last n) := by
  simp [mStarA]
end PI.WGB
