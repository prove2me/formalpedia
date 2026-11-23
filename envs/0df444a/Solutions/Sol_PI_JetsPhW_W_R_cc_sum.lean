-- Prove2me | solution 1 for PI.JetsPhW.W.R.cc_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:35.361336+00:00
-- url     : https://prove2.me/submissions/9905ad30-e35b-471e-8735-d7b7e7f6baa6

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
theorem _root_.solution {l : PowerSeries K} (hl0 : PowerSeries.constantCoeff l = 0) {τ : Type*}
    {a b : MvPowerSeries τ K} (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a l + PowerSeries.subst b l) = 0 := by
  rw [map_add, PowerSeries.constantCoeff_subst_eq_zero ha l hl0,
    PowerSeries.constantCoeff_subst_eq_zero hb l hl0, add_zero]
end PI.JetsPhW.W.R
