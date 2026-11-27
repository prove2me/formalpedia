-- Prove2me | solution 1 for PI.VolStabSW.densV_of_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:19:27.345137+00:00
-- url     : https://prove2.me/submissions/8df8473d-d2d1-439a-9fb5-68f9f97cc2a1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_HenselCountHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_MeasureEqOfCos
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVTop
import Theorems.Thm_PI_VolStabSW_cosDens_holds
import Theorems.Thm_PI_VolStabSW_densV_of_filt
import Theorems.Thm_PI_VolStabSW_henselCount_holds
import Theorems.Thm_PI_VolStabSW_tensAll_holds


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
theorem _root_.solution (hF : GramFilt) : DensV :=
  densV_of_filt henselCount_holds cosDens_holds tensAll_holds hF
end PI.VolStabSW
