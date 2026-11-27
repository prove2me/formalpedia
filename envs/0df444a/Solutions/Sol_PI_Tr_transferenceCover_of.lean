-- Prove2me | solution 1 for PI.Tr.transferenceCover_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:17:49.033799+00:00
-- url     : https://prove2.me/submissions/c7685d21-a808-448a-8f14-10dbbd357cec

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_Transference
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_TransferenceKey
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_DualTransport
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_Minima
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_Skeleton
import Theorems.Thm_PI_Tr_key_of_steps
import Theorems.Thm_PI_cover_of_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open PI PI.Tr
namespace PI.Tr
theorem _root_.solution (hP : PoissonBasis) (hB : DualTransport) (hG : GaussStep)
    (hS : KeySmall) : PI.TransferenceCover :=
  PI.cover_of_key (key_of_steps hP hB hG hS)
end PI.Tr
