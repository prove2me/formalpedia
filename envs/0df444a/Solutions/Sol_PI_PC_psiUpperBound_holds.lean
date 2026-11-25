-- Prove2me | solution 1 for PI.PC.psiUpperBound_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:43:42.493171+00:00
-- url     : https://prove2.me/submissions/8985ba50-4f35-4898-8c11-3bd1798be3d3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PrimeCountBoundOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_LogFactorialEqSumOfLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_LogFactorialLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PsiUpperBoundOfLtThirtyMulSixPow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PsiLowerBoundHolds
import Theorems.Thm_PI_PC_chUpper_of
import Theorems.Thm_PI_PC_chebyshevConstantNumeric
import Theorems.Thm_PI_PC_dUpper
import Theorems.Thm_PI_PC_sandwich


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.PC
namespace PI.PC
theorem _root_.solution : CHUpper := chUpper_of chebyshevConstantNumeric dUpper sandwich
end PI.PC
