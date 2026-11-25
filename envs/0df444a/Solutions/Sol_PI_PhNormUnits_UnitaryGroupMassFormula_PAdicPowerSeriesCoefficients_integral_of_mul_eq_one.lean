-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.integral_of_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:03:09.015879+00:00
-- url     : https://prove2.me/submissions/7d3c8c78-4f94-4a6c-a50c-95efac350eb1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerBis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_NormUnitsSubstitution
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_PAdicPowerSeriesCoefficients_integral_iff
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_PAdicPowerSeriesCoefficients_constantCoeff_lift

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
theorem _root_.solution {σ : Type*} {W V : MvPowerSeries σ ℂ_[p]} (hW : IntegralMv W)
    (h1 : MvPowerSeries.constantCoeff W = 1) (hWV : W * V = 1) : IntegralMv V := by
  obtain ⟨W', rfl⟩ := (integral_iff W).1 hW
  have hc : MvPowerSeries.constantCoeff W' = 1 := by
    apply Subtype.ext
    rw [constantCoeff_lift, h1]
    rfl
  have hu : IsUnit W' := MvPowerSeries.isUnit_iff_constantCoeff.2 (by rw [hc]; exact isUnit_one)
  obtain ⟨U, hU⟩ : ∃ U, W' * U = 1 := ⟨↑hu.unit⁻¹, hu.mul_val_inv⟩
  refine (integral_iff V).2 ⟨U, ?_⟩
  have h2 : MvPowerSeries.map (intRing p).subtype W' * MvPowerSeries.map (intRing p).subtype U = 1 := by
    rw [← map_mul, hU, map_one]
  linear_combination V * h2 - (MvPowerSeries.map (intRing p).subtype U) * hWV
end PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients
