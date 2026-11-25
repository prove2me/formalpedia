-- Prove2me | solution 1 for PI.VolStabW.fFCount_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:55:10.502846+00:00
-- url     : https://prove2.me/submissions/3b9614f0-7123-4e86-932e-1a7b4824fd96

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFT
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFIn
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFAll
import Theorems.Thm_PI_VolStabW_FFHS_fFInert_holds
import Theorems.Thm_PI_VolStabW_fFCount_of_inert


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.VolStabW
namespace PI.VolStabW
theorem _root_.solution : FFCount := fFCount_of_inert FFHS.fFInert_holds
end PI.VolStabW
