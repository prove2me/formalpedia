-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.int_mulBy_zp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:36:23.49561+00:00
-- url     : https://prove2.me/submissions/ebbf3e6b-373a-4f32-b29e-94fc8d97062d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_TendstoCoeffOfCont
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffVar
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_int_mulBy_nat
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_cont_mulBy
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_tendsto_coeff_of_cont


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
include hSub hex0 hinv
namespace PI.PhNormUnits.UnitaryGroupMassFormula
theorem _root_.solution (hC : CalcClosed) (hD : NatDense)
    (hIA : IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])) {τ : Type}
    (x : MvPowerSeries τ ℂ_[p]) (hx0 : MvPowerSeries.constantCoeff x = 0) (hx : IntegralMv x) (n : ℤ_[p]) :
    IntegralMv (mulBy l ex (zc n) x) := by

  obtain ⟨u, hu⟩ := hD p n
  have hcont := cont_mulBy hex0 hinv x hx0
  have hconv : ∀ e, Tendsto (fun k => MvPowerSeries.coeff e (mulBy l ex ((u k : ℕ) : ℂ_[p]) x)) atTop
      (𝓝 (MvPowerSeries.coeff e (mulBy l ex (zc n) x))) :=
    fun e => tendsto_coeff_of_cont (fun c => mulBy l ex c x) hcont hu e
  exact (hC p τ _ _ hconv).2 (fun k => int_mulBy_nat hSub hex0 hinv hIA x hx0 hx (u k))
end PI.PhNormUnits.UnitaryGroupMassFormula
