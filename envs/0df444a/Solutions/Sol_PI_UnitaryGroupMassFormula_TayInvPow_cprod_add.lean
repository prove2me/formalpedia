-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.TayInvPow.cprod_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:43:25.742338+00:00
-- url     : https://prove2.me/submissions/cb1d72a3-808d-4da1-9b83-43a08c2c52a1

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
theorem _root_.solution (c : σ →₀ A) (β γ : σ →₀ ℕ) : cprod c (β + γ) = cprod c β * cprod c γ :=
  Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)
end PI.UnitaryGroupMassFormula.TayInvPow
