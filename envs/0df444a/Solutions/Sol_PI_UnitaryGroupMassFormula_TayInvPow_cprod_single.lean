-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.TayInvPow.cprod_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:43:29.952146+00:00
-- url     : https://prove2.me/submissions/c81f6ca2-cb43-4ab8-a5da-ecd7e6539caf

import Definitions.Def_Formalism_PeriodIntegrals_TayInvPow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TaylorInversePower_SumMultinomialSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.TayInvPow
open MvPowerSeries
variable {σ : Type*} {A : Type*} [CommRing A]
namespace PI.UnitaryGroupMassFormula.TayInvPow
theorem _root_.solution (c : σ →₀ A) (p : σ) (n : ℕ) : cprod c (Finsupp.single p n) = c p ^ n :=
  Finsupp.prod_single_index (pow_zero _)
end PI.UnitaryGroupMassFormula.TayInvPow
