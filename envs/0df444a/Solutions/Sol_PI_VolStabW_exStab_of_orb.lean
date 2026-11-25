-- Prove2me | solution 1 for PI.VolStabW.exStab_of_orb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:19:57.603275+00:00
-- url     : https://prove2.me/submissions/27ec4f24-4196-4115-a098-1ee918a4a233

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExStabU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoClose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExStabFin
import Theorems.Thm_PI_VolStabW_exStab_of_U
import Theorems.Thm_PI_VolStabW_lcscPolish_holds
import Theorems.Thm_PI_VolStabW_secCtblW_holds


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
namespace PI.VolStabW
theorem _root_.solution (hO : OrbTup) (hI : NuInv) (hF : NuFin) (hN : NuNeZero) : ExStab :=
  exStab_of_U secCtblW_holds lcscPolish_holds hO hI hF hN
end PI.VolStabW
