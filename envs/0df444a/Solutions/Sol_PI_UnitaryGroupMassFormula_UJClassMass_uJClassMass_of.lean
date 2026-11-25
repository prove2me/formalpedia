-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.uJClassMass_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:41:30.702629+00:00
-- url     : https://prove2.me/submissions/2b4dc3e0-56ae-4220-9968-776af4012ad3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_Reduce
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UJClassMassAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_Development
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_uJClassMass_of_dict
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_dict_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (s1 : LatStep) (si : IsomStep) (s2 : EquivStep) (s3 : InjStep)
    (s4 : SurjStep) (s5 : CardStep) : PI.UJClassMass2.UJClassMass := by
  exact uJClassMass_of_dict (dict_of s1 si s2 s3 s4 s5)
end PI.UnitaryGroupMassFormula.UJClassMass
