-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.be_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:31:31.177133+00:00
-- url     : https://prove2.me/submissions/2bf3094a-af2a-41ce-96a2-87c2f9f172e0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_TendstoCoeffOfCont
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffVar
import Theorems.Thm_P2M_PI_PhNormUnits_UnitaryGroupMassFormula_add_zero___2ca64d39d994

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical Filter Topology MvPowerSeries.WithPiTopology
open PI PI.PhNormUnits PI.PhNormUnits.UnitaryGroupMassFormula
open PI.PhNormUnits
variable {p : ℕ} [Fact p.Prime]
variable (hE : CalcEquiv) (hSub : CalcSubst)
variable {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
  (hinv : PowerSeries.subst ex l = PowerSeries.X)
include hex0 hinv
namespace PI.PhNormUnits.UnitaryGroupMassFormula
theorem _root_.solution {τ : Type*} {ph : PowerSeries ℂ_[p]} (hph : PowerSeries.constantCoeff ph = 0)
    (z : MvPowerSeries τ ℂ_[p]) (hz : MvPowerSeries.constantCoeff z = 0) : be l ex ph z 0 = 0 := by

  unfold be
  rw [add_zero'' hex0 hinv z hz]
  unfold phAt
  rw [PowerSeries.subst_zero_of_constantCoeff_zero hph]
  ring
end PI.PhNormUnits.UnitaryGroupMassFormula
