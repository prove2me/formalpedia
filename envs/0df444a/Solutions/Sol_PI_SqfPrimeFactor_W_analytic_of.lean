-- Prove2me | solution 1 for PI.SqfPrimeFactor.W.analytic_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:39:02.097989+00:00
-- url     : https://prove2.me/submissions/d7a8fdb7-6130-4024-b393-5bd59721295e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_BigPrimes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_AnaCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_Analytic
import Theorems.Thm_PI_SqfPrimeFactor_W_ana_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.SqfPrimeFactor PI.SqfPrimeFactor.W
namespace PI.SqfPrimeFactor.W
theorem _root_.solution (hRS : PI.PrimesDyadicRS.Claim) : Analytic := by
  intro g r hr hg
  refine ana_main hRS g r hr hg (bigPrimes r) (fun p => ?_)
  simp only [bigPrimes, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨by omega, h⟩
end PI.SqfPrimeFactor.W
