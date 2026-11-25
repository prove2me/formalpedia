-- Prove2me | solution 1 for P2M_PI_Tr_transferenceMinima_of__e4ff42dc2360
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:44:54.371723+00:00
-- url     : https://prove2.me/submissions/73bbb581-b7e7-48a4-874a-be1c0720db60

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_Transference
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_TransferenceKey
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_DualTransport
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_Minima
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_Skeleton
import Theorems.Thm_PI_Tr_key_of
import Theorems.Thm_PI_minima_of_key


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
    PI.TransferenceMinima := PI.minima_of_key (key_of (hG hP) hS)
end PI.Tr
