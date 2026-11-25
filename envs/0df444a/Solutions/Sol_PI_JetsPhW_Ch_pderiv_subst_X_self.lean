-- Prove2me | solution 1 for PI.JetsPhW.Ch.pderiv_subst_X_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:04:36.585188+00:00
-- url     : https://prove2.me/submissions/68eb6d56-927f-4727-912d-17e3c700d718

import Definitions.Def_Formalism_PeriodIntegrals_JetsPhW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_CoeffPowEqZeroOfDegreeLt
import Theorems.Thm_PI_JetsPhW_Ch_pderiv_subst

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
theorem _root_.solution (i : σ) (g : PowerSeries R) :
    MvPowerSeries.pderiv R i (PowerSeries.subst (MvPowerSeries.X i) g) =
      PowerSeries.subst (MvPowerSeries.X i) (dX g) := by
  rw [pderiv_subst i (a := MvPowerSeries.X i) (MvPowerSeries.constantCoeff_X i) g,
    MvPowerSeries.pderiv_X_self, one_mul]
end PI.JetsPhW.Ch
