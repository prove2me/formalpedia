-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.norm_units_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:17:21.492009+00:00
-- url     : https://prove2.me/submissions/85084b31-1932-4ea7-963b-f570ff267d77

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerBis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_NormUnitsSubstitution
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_PAdicPowerSeriesCoefficients_coeff_expMv
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_PAdicPowerSeriesCoefficients_tendsto_coeff_pow

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
open PAdicPowerSeriesCoefficients
namespace PI.PhNormUnits.UnitaryGroupMassFormula
theorem _root_.solution : CalcClosed := by
  intro p _ σ F f hF
  refine ⟨fun h => ⟨?_, fun α => ?_⟩, fun h e => ?_⟩
  · rw [sub_zero, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    have hz : ∀ k, MvPowerSeries.coeff 0 (F k) = 0 := fun k => by
      have := (h k).1
      rwa [sub_zero, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at this
    refine tendsto_nhds_unique (hF 0) ?_
    simp only [hz]
    exact tendsto_const_nhds
  · have hk : ∀ k, ‖MvPowerSeries.coeff α (expMv (F k))‖ ≤ 1 := fun k => by
      have := (h k).2 α
      rw [sub_zero] at this
      exact this
    have ht : Tendsto (fun k => MvPowerSeries.coeff α (expMv (F k))) atTop
        (𝓝 (MvPowerSeries.coeff α (expMv f))) := by
      simp only [coeff_expMv]
      exact tendsto_finsetSum _ fun n _ => (tendsto_coeff_pow hF n α).div_const _
    show ‖MvPowerSeries.coeff α (expMv (f - 0))‖ ≤ 1
    rw [sub_zero]
    exact le_of_tendsto' ht.norm hk
  · exact le_of_tendsto' (hF e).norm fun k => h k e
end PI.PhNormUnits.UnitaryGroupMassFormula
