-- Prove2me | solution 1 for PI.VolStabSW.exFDStab_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:18:02.584077+00:00
-- url     : https://prove2.me/submissions/74157733-ee1f-4a9f-9d3c-d4d539363bae

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_ExFDStab
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoClose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_EqZeroOfMemNbhdA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_LocallyCompactAdelicUnitary
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_ExFDStabFin
import Theorems.Thm_PI_VolStabSW_discHF_holds
import Theorems.Thm_PI_VolStabSW_exFDStab_of
import Theorems.Thm_PI_VolStabSW_scha_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.VolStabSW
namespace PI.VolStabSW
theorem _root_.solution : ExFDStab := exFDStab_of scha_holds discHF_holds
end PI.VolStabSW
