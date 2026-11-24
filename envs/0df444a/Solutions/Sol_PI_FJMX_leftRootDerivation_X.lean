-- Prove2me | solution 1 for PI.FJMX.leftRootDerivation_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:24.631692+00:00
-- url     : https://prove2.me/submissions/90dc5436-f43a-4661-ade2-bd82db335e3a

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
theorem _root_.solution (a b : Ix p q) (v : Ln p q r s) :
    der1 a b (X v : Pol p q r s) = if linePos (a, v.2) = true then (if v.1 = b then X (a, v.2) else 0)
      else (if v.1 = a then -X (b, v.2) else 0) := by
  classical
  rw [der1, der_sum_apply, Finset.sum_eq_single v.2]
  · obtain ⟨v1, v2⟩ := v
    by_cases h : linePos (a, v2) = true
    · simp only [h, if_true, Derivation.smul_apply, pderiv_X, smul_eq_mul]
      by_cases hb : v1 = b
      · subst hb; simp
      · simp [Pi.single_apply, hb]
    · simp only [h, if_false, Derivation.neg_apply, Derivation.smul_apply, pderiv_X, smul_eq_mul]
      by_cases ha : v1 = a
      · subst ha; simp
      · simp [Pi.single_apply, ha]
  · intro c _ hc
    obtain ⟨v1, v2⟩ := v
    have h1 : (v1, v2) ≠ (b, c) := fun e => hc (by simp at e; exact e.2.symm)
    have h2 : (v1, v2) ≠ (a, c) := fun e => hc (by simp at e; exact e.2.symm)
    split_ifs <;> simp [pderiv_X, Pi.single_apply, h1.symm, h2.symm]
  · simp
end PI.FJMX
