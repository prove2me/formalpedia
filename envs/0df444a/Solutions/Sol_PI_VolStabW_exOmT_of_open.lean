-- Prove2me | solution 1 for PI.VolStabW.exOmT_of_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:03:50.069301+00:00
-- url     : https://prove2.me/submissions/b9e3a5c6-2a81-40d0-b5c8-06633b5bd9bd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocExOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibFour
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensFibInf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensFibV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExOmTOfSteps
import Theorems.Thm_P2M_PI_VolStabW_exOmT_of_steps__237885209129
import Theorems.Thm_PI_VolStabW_densFibInf_holds
import Theorems.Thm_PI_VolStabW_densFibV_holds


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
theorem _root_.solution (hI : FibInfEx) (hV : FibVEx) (hU : SdUniq) (hR : RestrProd) : ExOmT :=
  exOmT_of_steps' hI hV hU densFibInf_holds densFibV_holds hR
end PI.VolStabW
