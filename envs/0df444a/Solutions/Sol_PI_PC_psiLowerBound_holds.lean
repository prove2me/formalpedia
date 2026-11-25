-- Prove2me | solution 1 for PI.PC.psiLowerBound_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:43:40.393139+00:00
-- url     : https://prove2.me/submissions/d5b3f167-cdd1-4bd9-99c8-cacdfe366e57

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PrimeCountBoundOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_LogFactorialEqSumOfLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_LogFactorialLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PsiUpperBoundOfLtThirtyMulSixPow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PsiLowerBoundHolds
import Theorems.Thm_PI_PC_chLower_of
import Theorems.Thm_PI_PC_chebyshevConstantNumeric
import Theorems.Thm_PI_PC_dLower
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
theorem _root_.solution : CHLower := chLower_of chebyshevConstantNumeric dLower sandwich
end PI.PC
