-- Prove2me | solution 1 for PI.VolStabW.densAA_of_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:36:31.476372+00:00
-- url     : https://prove2.me/submissions/3ed42f1b-ddcf-442c-9511-beb3397c5122

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHIL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensVol
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHTop
import Theorems.Thm_PI_VolStabW_densAA_of
import Theorems.Thm_PI_VolStabW_fFCount_holds
import Theorems.Thm_PI_VolStabW_fibLat_holds
import Theorems.Thm_PI_VolStabW_idxAA_of
import Theorems.Thm_PI_VolStabW_idxL_holds
import Theorems.Thm_PI_VolStabW_latFacts_holds
import Theorems.Thm_PI_VolStabW_resAA_of


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
theorem _root_.solution (hV : VolAA) (hH : HensAA) (hI : IdxH) (hC : CntAA) : DensAA :=
  densAA_of fibLat_holds fFCount_holds
    (resAA_of hV latFacts_holds hH (idxAA_of idxL_holds hI) hC)
end PI.VolStabW
