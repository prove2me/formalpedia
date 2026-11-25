-- Prove2me | solution 1 for P2M_PI_PhNormUnits_UnitaryGroupMassFormula_add_zero___2ca64d39d994
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:25:27.355799+00:00
-- url     : https://prove2.me/submissions/98fdb197-a714-4fbb-a615-543f6a0bb248

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_TendstoCoeffOfCont
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffVar
import Theorems.Thm_P2M_PI_PhNormUnits_UnitaryGroupMassFormula_mulBy_zero__192bfb31d944
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_add_mulBy
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_mulBy_one


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
theorem _root_.solution {τ : Type*} (z : MvPowerSeries τ ℂ_[p]) (hz : MvPowerSeries.constantCoeff z = 0) :
    add l ex z 0 = z := by

  calc add l ex z 0 = add l ex (mulBy l ex 1 z) (mulBy l ex 0 z) := by
        rw [mulBy_one hex0 hinv z hz, mulBy_zero' hex0 z]
    _ = mulBy l ex (1 + 0) z := add_mulBy hex0 hinv 1 0 z hz
    _ = z := by rw [add_zero, mulBy_one hex0 hinv z hz]
end PI.PhNormUnits.UnitaryGroupMassFormula
