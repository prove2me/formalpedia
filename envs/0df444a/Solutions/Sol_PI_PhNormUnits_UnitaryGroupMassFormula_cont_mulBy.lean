-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.cont_mulBy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:14:55.645972+00:00
-- url     : https://prove2.me/submissions/d6282a7a-e38e-41cb-9cb2-02e04ba5a806

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_TendstoCoeffOfCont
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_cont_subst
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_constantCoeff_subst_log


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
variable {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
  (hinv : PowerSeries.subst ex l = PowerSeries.X)
include hex0 hinv
namespace PI.PhNormUnits.UnitaryGroupMassFormula
theorem _root_.solution {τ : Type*} (y : MvPowerSeries τ ℂ_[p]) (hy : MvPowerSeries.constantCoeff y = 0) :
    Continuous fun c : ℂ_[p] => mulBy l ex c y :=
  cont_subst (fun c => MvPowerSeries.C c * PowerSeries.subst y l) (continuous_C.mul continuous_const)
    (fun c => by rw [map_mul, constantCoeff_subst_log hex0 hinv y hy, mul_zero]) ex
end PI.PhNormUnits.UnitaryGroupMassFormula
