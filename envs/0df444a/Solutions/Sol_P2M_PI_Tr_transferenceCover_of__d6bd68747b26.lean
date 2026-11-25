-- Prove2me | solution 1 for P2M_PI_Tr_transferenceCover_of__d6bd68747b26
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:26:31.318319+00:00
-- url     : https://prove2.me/submissions/2b6e4144-76dc-4665-a8c2-bca432e0da70

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_Transference
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_TransferenceKey
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_DualTransport
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_Minima
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_Skeleton
import Theorems.Thm_PI_Tr_key_of
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
theorem _root_.solution (hP : PoissonGauss) (hG : GaussStep) (hS : KeySmall) :
    PI.TransferenceCover := PI.cover_of_key (key_of (hG hP) hS)
end PI.Tr
