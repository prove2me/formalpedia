-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.uJClassMass_of_dict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:11:01.377483+00:00
-- url     : https://prove2.me/submissions/7835259e-a096-4f59-ac85-a033acbc7c2d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_Reduce
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UJClassMassAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_Development
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_sum_eq_mass


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
theorem _root_.solution (hD : Dict) : PI.UJClassMass2.UJClassMass := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ hθ hτ hs hnd hL hsig n g hcov hdisj
  obtain ⟨Λ, ι, D⟩ := hD F E σ V h M b L0 hσ hθ hτ hs hnd hL hsig
  exact sum_eq_mass D n g hcov hdisj
end PI.UnitaryGroupMassFormula.UJClassMass
