-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.TayInvPow.coeff_F
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:17:50.636652+00:00
-- url     : https://prove2.me/submissions/2f096754-0dd6-4279-84de-72674b694e21

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
theorem _root_.solution (c : σ →₀ A) (t : A) (k : ℕ) (β : σ →₀ ℕ) : coeff β (F c t k) = cf c t k β := rfl
end PI.UnitaryGroupMassFormula.TayInvPow
