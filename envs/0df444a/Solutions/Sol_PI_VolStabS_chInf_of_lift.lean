-- Prove2me | solution 1 for PI.VolStabS.chInf_of_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:58:23.031001+00:00
-- url     : https://prove2.me/submissions/575261ec-0673-43b1-93b3-508a2f504ac7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensSAChar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensSAInt
import Theorems.Thm_PI_VolStabS_addIntF_holds
import Theorems.Thm_PI_VolStabS_chInf_of


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
open PI PI.VolStabS
namespace PI.VolStabS
theorem _root_.solution (hL : ChLift) : ChInf :=
  chInf_of hL addIntF_holds
end PI.VolStabS
