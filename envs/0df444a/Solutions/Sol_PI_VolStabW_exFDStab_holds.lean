-- Prove2me | solution 1 for PI.VolStabW.exFDStab_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:58:07.870704+00:00
-- url     : https://prove2.me/submissions/3f88ad4d-1ac9-490a-9c60-15ad7a7a8262

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExFDStab
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoClose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_EqZeroOfMemNbhdA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_LocallyCompactAdelicUnitary
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExFDStabFin
import Theorems.Thm_PI_VolStabW_discHF_holds
import Theorems.Thm_PI_VolStabW_exFDStab_of
import Theorems.Thm_PI_VolStabW_scha_holds


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
theorem _root_.solution : ExFDStab := exFDStab_of scha_holds discHF_holds
end PI.VolStabW
