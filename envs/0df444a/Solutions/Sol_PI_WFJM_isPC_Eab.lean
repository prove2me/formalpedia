-- Prove2me | solution 1 for PI.WFJM.isPC_Eab
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:25.213806+00:00
-- url     : https://prove2.me/submissions/dd57896c-bf48-4923-980b-1e822d97c486

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr

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
variable {p q r s : ℕ}
namespace PI.WFJM
theorem _root_.solution {n m : ℕ} (a b : Ix n m) (h : ¬ sameBlock a b) : IsPC (Eab a b) := by
  intro a' b' h'
  rw [FockH1Action.Eab, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact h h'
end PI.WFJM
