-- Prove2me | solution 1 for PI.VolStabSW.chInf_of_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:03:52.134891+00:00
-- url     : https://prove2.me/submissions/4c70852a-0c46-4d47-9382-14f1798965a8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensSAChar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensSAInt
import Theorems.Thm_PI_VolStabSW_addIntF_holds
import Theorems.Thm_PI_VolStabSW_chInf_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open scoped nonZeroDivisors
open PI PI.VolStabSW
namespace PI.VolStabSW
theorem _root_.solution (hL : ChLift) : ChInf :=
  chInf_of hL addIntF_holds
end PI.VolStabSW
