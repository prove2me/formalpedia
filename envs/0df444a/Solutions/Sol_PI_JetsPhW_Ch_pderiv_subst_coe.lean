-- Prove2me | solution 1 for PI.JetsPhW.Ch.pderiv_subst_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:44:21.522493+00:00
-- url     : https://prove2.me/submissions/6d7f72e6-60c8-42e0-aaf6-e355b9c037da

import Definitions.Def_Formalism_PeriodIntegrals_JetsPhW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_CoeffPowEqZeroOfDegreeLt
import Theorems.Thm_PI_JetsPhW_Ch_dX_eq

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
theorem _root_.solution (i : σ) {a : MvPowerSeries σ R} (ha : MvPowerSeries.constantCoeff a = 0)
    (q : Polynomial R) :
    MvPowerSeries.pderiv R i (PowerSeries.subst a (q : PowerSeries R)) =
      MvPowerSeries.pderiv R i a * PowerSeries.subst a (dX (q : PowerSeries R)) := by
  have hs : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [dX_eq, PowerSeries.derivative_coe, PowerSeries.subst_coe hs,
    PowerSeries.subst_coe hs, Derivation.map_aeval, smul_eq_mul]
  ring
end PI.JetsPhW.Ch
