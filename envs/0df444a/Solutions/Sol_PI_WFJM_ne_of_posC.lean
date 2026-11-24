-- Prove2me | solution 1 for PI.WFJM.ne_of_posC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:22.146492+00:00
-- url     : https://prove2.me/submissions/c0245e1e-d4c9-45da-8613-681568864c07

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
open MvPolynomial
namespace PI.WFJM
theorem _root_.solution {n k : ℕ} {a b : Ix n k} (h : posC a b) : a ≠ b := by
  rintro rfl
  rcases a with i | i <;>
    first
    | exact lt_irrefl i h
    | simp [FockH1Action.posC] at h
end PI.WFJM
