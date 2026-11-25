-- Prove2me | solution 1 for PI.ExpIntWProof.expIntW_of_key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:50:33.797923+00:00
-- url     : https://prove2.me/submissions/53eb4497-2dc9-4f1c-88b7-a1f163157801

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_InvNatCastMemWittIntegers
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_StepIII
import Theorems.Thm_PI_ExpIntWProof_stepIII_of_key
import Theorems.Thm_PI_ExpIntWProof_expIntW_of_steps


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.ExpIntWProof
open PI
namespace PI.ExpIntWProof
theorem _root_.solution (h1 : StepI) (h : KeyW) : ExpIntW :=
  expIntW_of_steps h1 (stepIII_of_key h)
end PI.ExpIntWProof
