-- Prove2me | solution 1 for PI.JetsPhW.W.R.l_ex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:45:09.752497+00:00
-- url     : https://prove2.me/submissions/d87bde33-38ab-4d72-8ee0-712f5a2763c2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_TwoUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_PolarizationDifferenceFormulaHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.JetsPhW PI.JetsPhW.W
open PI.JetsPhW
open PI.JetsPhW.W.R
variable {K : Type*} [CommRing K]
namespace PI.JetsPhW.W.R
theorem _root_.solution {l ex : PowerSeries K} (hex : PowerSeries.constantCoeff ex = 0)
    (hl : PowerSeries.subst ex l = PowerSeries.X) {τ : Type*} {x : MvPowerSeries τ K}
    (hx : MvPowerSeries.constantCoeff x = 0) :
    PowerSeries.subst (PowerSeries.subst x ex) l = x := by
  have ha : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex
  have hb : PowerSeries.HasSubst x := PowerSeries.HasSubst.of_constantCoeff_zero hx
  rw [← PowerSeries.subst_comp_subst_apply ha hb, hl, PowerSeries.subst_X hb]
end PI.JetsPhW.W.R
