-- Prove2me | solution 1 for PI.VolStabW.densV_of_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:51:17.945233+00:00
-- url     : https://prove2.me/submissions/5c435f9f-3ca8-4a98-b281-97bb336beb72

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_HenselCountHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_MeasureEqOfCos
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVTop
import Theorems.Thm_PI_VolStabW_cosDens_holds
import Theorems.Thm_PI_VolStabW_densV_of_filt
import Theorems.Thm_PI_VolStabW_henselCount_holds
import Theorems.Thm_PI_VolStabW_tensAll_holds


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
theorem _root_.solution (hF : GramFilt) : DensV :=
  densV_of_filt henselCount_holds cosDens_holds tensAll_holds hF
end PI.VolStabW
