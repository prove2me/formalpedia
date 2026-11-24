-- Prove2me | solution 1 for PI.FJMX.posPart_pw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:58.963807+00:00
-- url     : https://prove2.me/submissions/27ae004b-5eda-4fef-813b-0fb45dc1857f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistPad

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FockH1Action PI.FJM
noncomputable section
open PI PI.FJMX
namespace PI.FJMX
theorem _root_.solution (a : List ℤ) (ha : a.Pairwise (· ≥ ·)) : (PI.FJM.posPart a).Pairwise (· ≥ ·) := by
  rw [PI.FJM.posPart, List.pairwise_map]
  exact ha.imp fun h => by omega
end PI.FJMX
