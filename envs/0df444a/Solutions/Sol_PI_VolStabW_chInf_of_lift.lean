-- Prove2me | solution 1 for PI.VolStabW.chInf_of_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:08:43.843167+00:00
-- url     : https://prove2.me/submissions/77c73f8a-b1d1-4bb2-9bb6-c0952c97f07a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensSAChar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensSAInt
import Theorems.Thm_PI_VolStabW_addIntF_holds
import Theorems.Thm_PI_VolStabW_chInf_of


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
open PI PI.VolStabW
namespace PI.VolStabW
theorem _root_.solution (hL : ChLift) : ChInf := chInf_of hL addIntF_holds
end PI.VolStabW
