-- Prove2me | solution 1 for PI.WFJM.fockAct1_Eab
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:24.143814+00:00
-- url     : https://prove2.me/submissions/591c7c06-7d15-4aa1-a5c0-92cf1df6c800

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Theorems.Thm_PI_WFJM_fockAct1_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.WFJM
open MvPolynomial
open PI.FJM
namespace PI.WFJM
theorem _root_.solution (p q r s : ℕ) (a b : Ix p q) :
    fockAct1 p q r s (Eab a b) = ∑ c : Ix r s, omE (p := p) (q := q) (r := r) (s := s) (a, c) (b, c) := by
  rw [fockAct1_eq, Fintype.sum_eq_single a, Fintype.sum_eq_single b]
  · simp [FockH1Action.Eab, Matrix.single_apply]
  · intro x hx
    simp [FockH1Action.Eab, Matrix.single_apply, Ne.symm hx]
  · intro x hx
    simp [FockH1Action.Eab, Matrix.single_apply, Ne.symm hx]
end PI.WFJM
