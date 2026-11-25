-- Prove2me | solution 1 for P2M_PI_JetsPhW_Ch_subst_one__be9486c9456e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:44:37.307042+00:00
-- url     : https://prove2.me/submissions/cdab0619-86ab-428c-8ce9-0555ad2a65c3

import Definitions.Def_Formalism_PeriodIntegrals_JetsPhW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_CoeffPowEqZeroOfDegreeLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI.JetsPhW
open PI PI.JetsPhW PI.JetsPhW.Ch
variable {R : Type*} [CommRing R] {σ : Type*}
namespace PI.JetsPhW.Ch
theorem _root_.solution (a : MvPowerSeries σ R) : PowerSeries.subst a (1 : PowerSeries R) = 1 := by
  simpa using PowerSeries.subst_C (a := a) (1 : R)
end PI.JetsPhW.Ch
