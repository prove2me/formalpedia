-- Prove2me | solution 1 for PI.HookSteps.castSucc2_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:51:32.113978+00:00
-- url     : https://prove2.me/submissions/b700a74b-56d3-4312-b256-420868e4be4a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DetShiftNormOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_HookNorm
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open PI PI.HookSteps
namespace PI.HookSteps
theorem _root_.solution (n : ℕ) :
    Function.Injective (fun v : Fin n × Fin n => (Fin.castSucc v.1, Fin.castSucc v.2)) := by
  intro a b h
  simp only [Prod.mk.injEq, Fin.castSucc_inj] at h
  exact Prod.ext h.1 h.2
end PI.HookSteps
