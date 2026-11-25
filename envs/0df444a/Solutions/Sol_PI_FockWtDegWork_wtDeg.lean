-- Prove2me | solution 1 for PI.FockWtDegWork.wtDeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:09:36.23757+00:00
-- url     : https://prove2.me/submissions/22aff4d0-0086-4ccc-a61f-9ab792231745

import Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockWeightDegree_ExistsMonomialWeight
import Theorems.Thm_PI_FockWtDegWork_half1
import Theorems.Thm_PI_FockWtDegWork_half2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockH1Action
open PI PI.FockWtDegWork
namespace PI.FockWtDegWork
theorem _root_.solution : PI.FockDegreeTwoParts.WtDeg :=
  fun p q r s => ⟨half1 p q r s, half2 p q r s⟩
end PI.FockWtDegWork
