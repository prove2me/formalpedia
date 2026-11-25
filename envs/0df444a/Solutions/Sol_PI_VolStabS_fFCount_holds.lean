-- Prove2me | solution 1 for PI.VolStabS.fFCount_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:48:26.895918+00:00
-- url     : https://prove2.me/submissions/11c33034-3327-47ff-8539-ec570d065159

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFT
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFIn
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFAll
import Theorems.Thm_PI_VolStabS_FFHS_fFInert_holds
import Theorems.Thm_PI_VolStabS_fFCount_of_inert


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.VolStabS
namespace PI.VolStabS
theorem _root_.solution : FFCount := fFCount_of_inert FFHS.fFInert_holds
end PI.VolStabS
