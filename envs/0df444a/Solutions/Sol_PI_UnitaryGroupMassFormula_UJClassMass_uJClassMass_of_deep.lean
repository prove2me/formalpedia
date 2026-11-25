-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.uJClassMass_of_deep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:50:38.898515+00:00
-- url     : https://prove2.me/submissions/310b54cc-3001-462f-bd19-72959c718816

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_EquivFunLinOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_CardStepOf
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_injStep_of
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_cardStep_of
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_equivStep
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_isomStep
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_uJClassMass_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (hR : PI.UnitaryGroupMassFormula.UJClassFin.RatDense) (hC : CrdBounds) (s1 : LatStep) (s4 : SurjStep) :
    PI.UJClassMass2.UJClassMass :=
  uJClassMass_of s1 isomStep equivStep (injStep_of hR hC) s4 (cardStep_of hR hC)
end PI.UnitaryGroupMassFormula.UJClassMass
