-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.TayInvPow.deg_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:43:32.478178+00:00
-- url     : https://prove2.me/submissions/6b2288f1-d48c-431f-9351-01a5d283135c

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
theorem _root_.solution (β γ : σ →₀ ℕ) : deg (β + γ) = deg β + deg γ :=
  Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)
end PI.UnitaryGroupMassFormula.TayInvPow
