-- Prove2me | solution 1 for PI.FJMX.rightRootOperator_eq_derivation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:38:44.744563+00:00
-- url     : https://prove2.me/submissions/9491d003-b366-4985-a80e-e4fb756163f5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistHW
import Theorems.Thm_PI_FJMX_der_sum_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial FockH1Action PI.FJM
noncomputable section
open PI PI.FJMX
variable {p q r s : ℕ}
namespace PI.FJMX
theorem _root_.solution (c d : Ix r s) (hcd : c ≠ d) (hblk : ∀ a : Ix p q, linePos (a, c) = linePos (a, d))
    (f : Pol p q r s) : rai2 (p := p) (q := q) c d f = der2 c d f := by
  classical
  rw [rai2, der2, der_sum_apply, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [Module.End.mul_apply, raiB, lowB, ← hblk a]
  by_cases h : linePos (a, c) = true
  · simp [h, smul_eq_mul]
  · have hne : (a, c) ≠ (a, d) := fun e => hcd (by simp at e; exact e)
    simp only [h, if_false, Bool.false_eq_true, LinearMap.neg_apply, LinearMap.mulLeft_apply,
      Derivation.coeFn_coe, Derivation.neg_apply, Derivation.smul_apply, smul_eq_mul]
    rw [pderiv_mul, pderiv_X_of_ne hne.symm]
    ring
end PI.FJMX
