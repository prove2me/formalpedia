-- Prove2me | solution 1 for PI.HookSteps.rowGen_coeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:00:22.800382+00:00
-- url     : https://prove2.me/submissions/a4ec0147-a7f8-4267-a395-4bdefc5d1596

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DetShiftNormOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LGradedLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockqLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DetShift
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
theorem _root_.solution (a b : Fin N) (f : MvPolynomial (Fin N × Fin N) ℚ) :
    (rowGen ℚ a b f).coeff 0 = f := by
  induction f using MvPolynomial.induction_on
  · next c =>
    simp [rowGen, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
  · next p q hp hq =>
    rw [map_add, Polynomial.coeff_add, hp, hq]
  · next p v hp =>
    rw [map_mul, Polynomial.mul_coeff_zero, hp]
    simp only [rowGen, MvPolynomial.aeval_X]
    split_ifs <;> simp
end PI.HookSteps
