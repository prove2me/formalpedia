-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.exp_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:10:37.68182+00:00
-- url     : https://prove2.me/submissions/514521fe-e0da-44b2-9a22-6e2d8f3343d8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerBis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_NormUnitsSubstitution
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_PAdicPowerSeriesCoefficients_exp_X0_add_X1
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_PAdicPowerSeriesCoefficients_subst_exp

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
theorem _root_.solution {σ : Type*} {F G : MvPowerSeries σ ℂ_[p]} (hF : MvPowerSeries.constantCoeff F = 0)
    (hG : MvPowerSeries.constantCoeff G = 0) :
    PowerSeries.subst (F + G) (PowerSeries.exp ℂ_[p]) =
      PowerSeries.subst F (PowerSeries.exp ℂ_[p]) * PowerSeries.subst G (PowerSeries.exp ℂ_[p]) := by
  have hb : MvPowerSeries.HasSubst ![F, G] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simp [hF, hG])
  have h0 : MvPowerSeries.subst ![F, G] (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) = F := by
    rw [MvPowerSeries.subst_X hb]; rfl
  have h1 : MvPowerSeries.subst ![F, G] (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) = G := by
    rw [MvPowerSeries.subst_X hb]; rfl
  have h01 : MvPowerSeries.subst ![F, G] (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) =
      F + G := by
    rw [MvPowerSeries.subst_add hb, h0, h1]
  rw [← h01, ← subst_exp hb (by simp), exp_X0_add_X1, MvPowerSeries.subst_mul hb,
    subst_exp hb (by simp), subst_exp hb (by simp), h0, h1]
end PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients
