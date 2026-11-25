-- Prove2me | solution 1 for PI.FrameInd.negative_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:15:08.934799+00:00
-- url     : https://prove2.me/submissions/1b9b0c10-f914-4fef-90df-641ab5e0d153

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_NegBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_EqZeroOfNegMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_NegativeBound
import Theorems.Thm_PI_FrameInd_NegB_negBound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
noncomputable section
open PI PI.FrameInd
namespace PI.FrameInd
theorem _root_.solution : NegBound := fun k r S hS => NegB.negBound k r S hS
end PI.FrameInd
