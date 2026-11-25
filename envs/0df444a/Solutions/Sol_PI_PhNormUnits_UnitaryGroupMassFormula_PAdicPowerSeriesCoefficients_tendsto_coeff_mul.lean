-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.tendsto_coeff_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:03:40.051371+00:00
-- url     : https://prove2.me/submissions/a185041a-4785-4102-9cc3-03bc3b002b34

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerBis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_NormUnitsSubstitution

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open PI PI.PhNormUnits PI.PhNormUnits.UnitaryGroupMassFormula
open PI.PhNormUnits
open PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients
variable {p : ℕ} [Fact p.Prime]
namespace PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients
theorem _root_.solution {σ : Type*} {F G : ℕ → MvPowerSeries σ ℂ_[p]} {f g : MvPowerSeries σ ℂ_[p]}
    (hF : ∀ e, Tendsto (fun k => MvPowerSeries.coeff e (F k)) atTop (𝓝 (MvPowerSeries.coeff e f)))
    (hG : ∀ e, Tendsto (fun k => MvPowerSeries.coeff e (G k)) atTop (𝓝 (MvPowerSeries.coeff e g)))
    (e : σ →₀ ℕ) :
    Tendsto (fun k => MvPowerSeries.coeff e (F k * G k)) atTop (𝓝 (MvPowerSeries.coeff e (f * g))) := by
  simp only [MvPowerSeries.coeff_mul]
  exact tendsto_finsetSum _ fun i _ => (hF i.1).mul (hG i.2)
end PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients
