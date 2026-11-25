-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.cont_be
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:24:57.752897+00:00
-- url     : https://prove2.me/submissions/69370fa3-47d8-4ab8-9a8c-beea529c65a4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_TendstoCoeffOfCont
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_cont_subst
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_cont_mulBy
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_L_mulBy
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_constantCoeff_formalAdd
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_constantCoeff_formalSMul
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
theorem _root_.solution {τ : Type*} (ph : PowerSeries ℂ_[p]) (z y : MvPowerSeries τ ℂ_[p])
    (hz : MvPowerSeries.constantCoeff z = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    Continuous fun c : ℂ_[p] => be l ex ph z (mulBy l ex c y) := by
  have hA : Continuous fun c : ℂ_[p] => add l ex z (mulBy l ex c y) := by
    have : (fun c : ℂ_[p] => add l ex z (mulBy l ex c y)) = fun c =>
        PowerSeries.subst (PowerSeries.subst z l + MvPowerSeries.C c * PowerSeries.subst y l) ex := by
      funext c; unfold add; rw [L_mulBy hex0 hinv c y hy]
    rw [this]
    exact cont_subst (fun c : ℂ_[p] => PowerSeries.subst z l + MvPowerSeries.C c * PowerSeries.subst y l)
      (continuous_const.add (continuous_C.mul continuous_const))
      (fun c => by
        show MvPowerSeries.constantCoeff (PowerSeries.subst z l + MvPowerSeries.C c * PowerSeries.subst y l) = 0
        rw [map_add, map_mul, constantCoeff_subst_log hex0 hinv y hy, constantCoeff_subst_log hex0 hinv z hz]; simp) ex
  unfold be
  refine ((cont_subst _ hA (fun c => constantCoeff_formalAdd hex0 hinv _ _ hz (constantCoeff_formalSMul hex0 hinv c y hy)) ph).sub
    continuous_const).sub ?_
  exact cont_subst _ (cont_mulBy hex0 hinv y hy) (fun c => constantCoeff_formalSMul hex0 hinv c y hy) ph
end PI.PhNormUnits.UnitaryGroupMassFormula
