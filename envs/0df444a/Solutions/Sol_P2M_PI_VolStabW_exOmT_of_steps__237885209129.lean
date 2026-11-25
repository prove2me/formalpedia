-- Prove2me | solution 1 for P2M_PI_VolStabW_exOmT_of_steps__237885209129
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:40:21.60239+00:00
-- url     : https://prove2.me/submissions/11cfae5d-8723-43f6-ae64-9cbb5dcfe9ad

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocExOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibFour
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensFibInf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensFibV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExOmTOfSteps
import Theorems.Thm_PI_VolStabW_latSB_holds
import Theorems.Thm_PI_VolStabW_exOmT_of_steps


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
namespace PI.VolStabW
theorem _root_.solution (hI : FibInfEx) (hV : FibVEx) (hU : SdUniq) (hDI : DensFibInf)
    (hDV : DensFibV) (hR : RestrProd) : ExOmT :=
  exOmT_of_steps hI hV latSB_holds hU hDI hDV hR
end PI.VolStabW
