-- Prove2me | solution 1 for PI.FJMD.negPart_length
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:41.907664+00:00
-- url     : https://prove2.me/submissions/df35e3fa-fc02-4ae6-8519-5af2835598fd

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
theorem _root_.solution (b : List ℤ) : (PI.FJM.negPart b).length = b.length := by
  simp [PI.FJM.negPart]
end PI.FJMD
