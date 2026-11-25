-- Prove2me | solution 1 for PI.HookSteps.polynomial_eq_divisibility
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:18:26.727859+00:00
-- url     : https://prove2.me/submissions/ce7d00d4-1679-4a74-8455-57530d52cbc6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DetShiftNormOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LGradedLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockqLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DetShift
import Theorems.Thm_PI_HookSteps_rowDiv_one_mul_X
import Theorems.Thm_PI_HookSteps_polE_apply
import Theorems.Thm_PI_HookSteps_polE_mul_X
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
variable {N : ℕ}
namespace PI.HookSteps
theorem _root_.solution : PolEqRowDiv := by
  intro N a b f
  induction f using MvPolynomial.induction_on
  · next c =>
    rw [polE_apply]
    simp [rowDiv, rowGen, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
  · next p q hp hq =>
    rw [map_add, hp, hq]
    simp only [rowDiv, map_add, Polynomial.coeff_add]
  · next p v hp =>
    rw [polE_mul_X, rowDiv_one_mul_X, hp]
end PI.HookSteps
