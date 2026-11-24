-- Prove2me | solution 1 for PI.FJMX.rightRootDerivation_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:00.244002+00:00
-- url     : https://prove2.me/submissions/89f3a52e-72ff-4e3c-96a4-56948885dacb

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
theorem _root_.solution (c d : Ix r s) (v : Ln p q r s) :
    der2 c d (X v : Pol p q r s) = if linePos (v.1, c) = true then (if v.2 = d then X (v.1, c) else 0)
      else (if v.2 = c then -X (v.1, d) else 0) := by
  classical
  rw [der2, der_sum_apply, Finset.sum_eq_single v.1]
  · obtain ⟨v1, v2⟩ := v
    by_cases h : linePos (v1, c) = true
    · simp only [h, if_true, Derivation.smul_apply, pderiv_X, smul_eq_mul]
      by_cases hb : v2 = d
      · subst hb; simp
      · simp [Pi.single_apply, hb]
    · simp only [h, if_false, Derivation.neg_apply, Derivation.smul_apply, pderiv_X, smul_eq_mul]
      by_cases ha : v2 = c
      · subst ha; simp
      · simp [Pi.single_apply, ha]
  · intro a _ hc
    obtain ⟨v1, v2⟩ := v
    have h1 : (v1, v2) ≠ (a, d) := fun e => hc (by simp at e; exact e.1.symm)
    have h2 : (v1, v2) ≠ (a, c) := fun e => hc (by simp at e; exact e.1.symm)
    split_ifs <;> simp [pderiv_X, Pi.single_apply, h1.symm, h2.symm]
  · simp
end PI.FJMX
