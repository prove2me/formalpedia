-- Prove2me | solution 1 for PI.WFJM.fockAct2_Eab
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:44.227794+00:00
-- url     : https://prove2.me/submissions/51372282-d92e-4db3-92d3-c5ee0be7d99f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Theorems.Thm_PI_WFJM_fockAct2_eq

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
theorem _root_.solution (p q r s : ℕ) (c d : Ix r s) :
    fockAct2 p q r s (Eab c d) = ∑ a : Ix p q, omE (p := p) (q := q) (r := r) (s := s) (a, c) (a, d) := by
  rw [fockAct2_eq]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_eq_single c, Fintype.sum_eq_single d]
  · simp [FockH1Action.Eab, Matrix.single_apply]
  · intro x hx
    simp [FockH1Action.Eab, Matrix.single_apply, Ne.symm hx]
  · intro x hx
    simp [FockH1Action.Eab, Matrix.single_apply, Ne.symm hx]
end PI.WFJM
