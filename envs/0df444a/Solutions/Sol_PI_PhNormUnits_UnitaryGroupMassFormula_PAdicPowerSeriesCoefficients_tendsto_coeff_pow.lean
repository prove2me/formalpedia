-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.tendsto_coeff_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:10:00.834851+00:00
-- url     : https://prove2.me/submissions/28bbb303-8245-42ca-b378-ded5fa3e330f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerBis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_NormUnitsSubstitution
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_PAdicPowerSeriesCoefficients_tendsto_coeff_mul

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
theorem _root_.solution {σ : Type*} {F : ℕ → MvPowerSeries σ ℂ_[p]} {f : MvPowerSeries σ ℂ_[p]}
    (hF : ∀ e, Tendsto (fun k => MvPowerSeries.coeff e (F k)) atTop (𝓝 (MvPowerSeries.coeff e f)))
    (n : ℕ) :
    ∀ e, Tendsto (fun k => MvPowerSeries.coeff e (F k ^ n)) atTop (𝓝 (MvPowerSeries.coeff e (f ^ n))) := by
  induction n with
  | zero => intro e; simp only [pow_zero]; exact tendsto_const_nhds
  | succ n ih => intro e; simp only [pow_succ]; exact tendsto_coeff_mul ih hF e
end PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients
