-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CommMult.schurStep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:39:05.013447+00:00
-- url     : https://prove2.me/submissions/a7fd420b-5c06-47d3-b442-865e0ce96eb7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CommutingMultiplicity_SchurStep
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchurIrreducible
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CommutingMultiplicity_SchurStepAlt
import Theorems.Thm_UpperTheory_Reformulated_B_SchurIrreducible_schurStep


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CommMult
open Matrix
namespace PI.UnitaryGroupMassFormula.CommMult
theorem _root_.solution : SchurStep :=
  _root_.UpperTheory.Reformulated.B.SchurIrreducible.schurStep
end PI.UnitaryGroupMassFormula.CommMult
