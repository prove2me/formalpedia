-- Prove2me | solution 1 for PI.FJMD.posPart_length
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:42.398233+00:00
-- url     : https://prove2.me/submissions/f35b683b-0d09-4deb-8b6e-8c12bdf0544b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeProdVarMatNeZero

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
open PI PI.FJMD
open PI.FJM
namespace PI.FJMD
theorem _root_.solution (a : List ℤ) : (PI.FJM.posPart a).length = a.length := by
  simp [PI.FJM.posPart]
end PI.FJMD
