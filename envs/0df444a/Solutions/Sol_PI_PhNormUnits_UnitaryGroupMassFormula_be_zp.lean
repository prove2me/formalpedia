-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.be_zp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:41:39.062406+00:00
-- url     : https://prove2.me/submissions/ba9465a5-98ae-4ea9-b143-2450aba452ce

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_TendstoCoeffOfCont
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffVar
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_be_nat
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_cont_be
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
variable {ph : PowerSeries ℂ_[p]}
  (hB : Simeq (be l ex ph (add l ex (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (be l ex ph (Xv 0) (Xv 2) + be l ex ph (Xv 1) (Xv 2)))
include hE hSub hex0 hinv hB
namespace PI.PhNormUnits.UnitaryGroupMassFormula
theorem _root_.solution (hC : CalcClosed) (hD : NatDense) (hph : PowerSeries.constantCoeff ph = 0)
    (hIA : IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])) {τ : Type}
    (z y : MvPowerSeries τ ℂ_[p]) (hz0 : MvPowerSeries.constantCoeff z = 0)
    (hy0 : MvPowerSeries.constantCoeff y = 0) (hz : IntegralMv z) (hy : IntegralMv y) (n : ℤ_[p]) :
    Simeq (be l ex ph z (mulBy l ex (zc n) y)) (MvPowerSeries.C (zc n) * be l ex ph z y) := by

  obtain ⟨u, hu⟩ := hD p n
  let F : ℂ_[p] → MvPowerSeries τ ℂ_[p] := fun c => be l ex ph z (mulBy l ex c y) - MvPowerSeries.C c * be l ex ph z y
  have hcont : Continuous F := by
    refine (cont_be hex0 hinv ph z y hz0 hy0).sub ?_
    refine continuous_pi (fun e => ?_)
    show Continuous (fun c : ℂ_[p] => MvPowerSeries.coeff e (MvPowerSeries.C c * be l ex ph z y))
    simp only [MvPowerSeries.coeff_C_mul]
    exact continuous_id.mul continuous_const
  have hconv : ∀ e, Tendsto (fun k => MvPowerSeries.coeff e (F ((u k : ℕ) : ℂ_[p]))) atTop
      (𝓝 (MvPowerSeries.coeff e (F (zc n)))) :=
    fun e => tendsto_coeff_of_cont F hcont hu e
  have hk : ∀ k, Simeq (F ((u k : ℕ) : ℂ_[p])) 0 := fun k =>
    ((hE p τ _ _ 0 0).2.2.2.2.2).mp (be_nat hE hSub hex0 hinv hB hph hIA z y hz0 hy0 hz hy (u k))
  have h1 := (hC p τ (fun k => F ((u k : ℕ) : ℂ_[p])) (F (zc n)) hconv).1 hk
  exact ((hE p τ _ _ 0 0).2.2.2.2.2).mpr h1
end PI.PhNormUnits.UnitaryGroupMassFormula
