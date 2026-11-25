-- Prove2me | solution 1 for PI.VolStabW.exStab_of_nu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:42:27.036835+00:00
-- url     : https://prove2.me/submissions/8a280e6d-6708-44d4-bf1e-908d62e685fd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExStabFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_OrbTupFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExStabOrb
import Theorems.Thm_PI_VolStabW_exStab_of_orb
import Theorems.Thm_PI_VolStabW_orbTup_holds


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
theorem _root_.solution (hI : NuInv) (hF : NuFin) (hN : NuNeZero) : ExStab :=
  exStab_of_orb orbTup_holds hI hF hN
end PI.VolStabW
