-- Prove2me | solution 1 for PI.JetsPhW.W.phAt_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:55:07.583855+00:00
-- url     : https://prove2.me/submissions/ff9ad56f-37e9-4f98-b8d3-5d739f7bfd9b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_TwoUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_PolarizationDifferenceFormulaHolds
import Theorems.Thm_PI_JetsPhW_W_R_cc_l
import Theorems.Thm_PI_JetsPhW_W_R_ph_ex
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
    phAt ph (add l ex a b) = PowerSeries.subst (PowerSeries.subst a l + PowerSeries.subst b l) (psi ex ph) := by
  unfold PI.JetsPhW.phAt PI.JetsPhW.add psi
  exact PI.JetsPhW.W.R.ph_ex hex
    (PI.JetsPhW.W.R.cc_sum (PI.JetsPhW.W.R.cc_l hex hl) ha hb)
end PI.JetsPhW.W
