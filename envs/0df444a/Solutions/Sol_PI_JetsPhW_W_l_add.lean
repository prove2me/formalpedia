-- Prove2me | solution 1 for PI.JetsPhW.W.l_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:54:59.213405+00:00
-- url     : https://prove2.me/submissions/5b729fd9-25ef-4c7f-a4df-a13c16796ca8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_TwoUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_PolarizationDifferenceFormulaHolds
import Theorems.Thm_PI_JetsPhW_W_R_cc_l
import Theorems.Thm_PI_JetsPhW_W_R_l_ex
import Theorems.Thm_PI_JetsPhW_W_R_cc_sum

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
variable {p : ℕ} [Fact p.Prime] {σ : Type*} {l ex ph : PowerSeries ℂ_[p]}
namespace PI.JetsPhW.W
theorem _root_.solution (hex : PowerSeries.constantCoeff ex = 0) (hl : PowerSeries.subst ex l = PowerSeries.X)
    {a b : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) :
    PowerSeries.subst (add l ex a b) l = PowerSeries.subst a l + PowerSeries.subst b l := by
  unfold PI.JetsPhW.add
  exact PI.JetsPhW.W.R.l_ex hex hl
    (PI.JetsPhW.W.R.cc_sum (PI.JetsPhW.W.R.cc_l hex hl) ha hb)
end PI.JetsPhW.W
