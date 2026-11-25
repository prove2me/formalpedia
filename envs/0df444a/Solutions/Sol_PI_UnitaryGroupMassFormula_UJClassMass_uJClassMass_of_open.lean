-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.uJClassMass_of_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:25:14.3208+00:00
-- url     : https://prove2.me/submissions/0e055f02-584a-4a65-b853-eec7c8c3f0bc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_UJClassMassOfDeep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_RationalPointsDense
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_UJClassMassOfOpen
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_UJClassMass_uJClassMass_of_deep__8bf3fe32cfe9
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_rational_points_dense


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (s1 : LatStep) (s4 : SurjStep) : PI.UJClassMass2.UJClassMass :=
  uJClassMass_of_deep' PI.UnitaryGroupMassFormula.UJClassFin.rational_points_dense s1 s4
end PI.UnitaryGroupMassFormula.UJClassMass
