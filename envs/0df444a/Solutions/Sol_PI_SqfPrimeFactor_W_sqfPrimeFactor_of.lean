-- Prove2me | solution 1 for PI.SqfPrimeFactor.W.sqfPrimeFactor_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:14:15.989322+00:00
-- url     : https://prove2.me/submissions/cfaada1f-746a-4238-b31f-dbce8d835eb7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_ClaimOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_SquarefreeCountEstimate
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_IrreducibleCountLowerBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_Analytic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_SqfPrimeFactorOf
import Theorems.Thm_PI_SqfPrimeFactor_W_analytic_of
import Theorems.Thm_PI_SqfPrimeFactor_W_claim_of
import Theorems.Thm_PI_SqfPrimeFactor_W_irreducible_count_lower_bound
import Theorems.Thm_PI_SqfPrimeFactor_W_squarefree_count_estimate


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.SqfPrimeFactor PI.SqfPrimeFactor.W
namespace PI.SqfPrimeFactor.W
theorem _root_.solution (hRS : PI.PrimesDyadicRS.Claim) : PI.SqfPrimeFactor.Claim :=
  claim_of squarefree_count_estimate irreducible_count_lower_bound (analytic_of hRS)
end PI.SqfPrimeFactor.W
