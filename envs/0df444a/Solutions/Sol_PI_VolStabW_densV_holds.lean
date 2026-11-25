-- Prove2me | solution 1 for PI.VolStabW.densV_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:06:39.196438+00:00
-- url     : https://prove2.me/submissions/e740d424-56df-4b8b-888e-a933a1eecb53

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVDx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVSec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExistsUnifFv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVAll
import Theorems.Thm_PI_VolStabW_densV_of_gram
import Theorems.Thm_PI_VolStabW_dxOpen_of
import Theorems.Thm_PI_VolStabW_gramFilt_of
import Theorems.Thm_PI_VolStabW_secGram_holds


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
theorem _root_.solution : DensV :=
  densV_of_gram (gramFilt_of (dxOpen_of secGram_holds))
end PI.VolStabW
