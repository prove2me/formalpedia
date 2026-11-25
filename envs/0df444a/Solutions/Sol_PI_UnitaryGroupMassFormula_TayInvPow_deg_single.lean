-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.TayInvPow.deg_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:43:36.494854+00:00
-- url     : https://prove2.me/submissions/c807a6cb-8094-4f76-8aaf-cbe96b836a74

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
theorem _root_.solution (p : σ) (n : ℕ) : deg (Finsupp.single p n) = n :=
  Finsupp.sum_single_index rfl
end PI.UnitaryGroupMassFormula.TayInvPow
