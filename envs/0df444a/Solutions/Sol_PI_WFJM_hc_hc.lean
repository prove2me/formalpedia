-- Prove2me | solution 1 for PI.WFJM.hc_hc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:09.532801+00:00
-- url     : https://prove2.me/submissions/db024059-ffae-432d-ab80-332497ca4816

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
open MvPolynomial
variable {σ : Type*}
namespace PI.WFJM
theorem _root_.solution (m n : ℕ) (P : MvPolynomial σ ℂ) :
    homogeneousComponent m (homogeneousComponent n P) =
      if m = n then homogeneousComponent n P else 0 := by
  exact homogeneousComponent_of_mem (homogeneousComponent_mem n P)
end PI.WFJM
