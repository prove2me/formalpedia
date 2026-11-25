-- Prove2me | solution 1 for commutant_multiplicity_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:03:55.469305+00:00
-- url     : https://prove2.me/submissions/ad968f27-f9da-4b11-bdd7-77a8f72fa856

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CommutingMultiplicity_CommMultOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CommutingMultiplicity_SchurStepAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CommutingMultiplicity_InjStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CommutingMultiplicity_IntegrableEntry
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_CommMult
import Theorems.Thm_PI_UnitaryGroupMassFormula_CommMult_avStep
import Theorems.Thm_PI_UnitaryGroupMassFormula_CommMult_commMult_of
import Theorems.Thm_PI_UnitaryGroupMassFormula_CommMult_injStep
import Theorems.Thm_PI_UnitaryGroupMassFormula_CommMult_schurStep
import Theorems.Thm_UpperTheory_Reformulated_B_SchurIrreducible_schurStep


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.UMultOne.CommutantMult :=
  PI.UnitaryGroupMassFormula.CommMult.commMult_of PI.UnitaryGroupMassFormula.CommMult.schurStep PI.UnitaryGroupMassFormula.CommMult.injStep PI.UnitaryGroupMassFormula.CommMult.avStep
