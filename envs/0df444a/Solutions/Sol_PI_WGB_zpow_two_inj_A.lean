-- Prove2me | solution 1 for PI.WGB.zpow_two_inj_A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:11:38.850516+00:00
-- url     : https://prove2.me/submissions/6723ceb7-79b3-4b94-9497-3c8be2052735

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFacts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFactsProofA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetEmbUnitriA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_CoeffRowActDiagA
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
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
variable {n : ℕ}
namespace PI.WGB
theorem _root_.solution (a b : ℤ) (h : (2 : ℂ) ^ a = 2 ^ b) : a = b := by
  have h2 := congrArg (fun z : ℂ => ‖z‖) h
  simp only [norm_zpow] at h2
  have h3 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h3] at h2
  exact zpow_right_injective₀ (by norm_num : (0:ℝ) < 2) (by norm_num) h2
end PI.WGB
