-- Prove2me | solution 1 for P2M_PI_UnitaryGroupMassFormula_UJClassMass_uJClassMass_of_deep__8bf3fe32cfe9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:06:25.776729+00:00
-- url     : https://prove2.me/submissions/2fc7f2fe-51ae-460c-baf6-4fe418cb2e7c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_CardStepOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_UJClassMassOfDeep
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_crdBounds
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_uJClassMass_of_deep


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (hR : PI.UnitaryGroupMassFormula.UJClassFin.RatDense) (s1 : LatStep) (s4 : SurjStep) :
    PI.UJClassMass2.UJClassMass :=
  uJClassMass_of_deep hR crdBounds s1 s4
end PI.UnitaryGroupMassFormula.UJClassMass
