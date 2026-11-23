-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.integral_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:12.011101+00:00
-- url     : https://prove2.me/submissions/e7fa79f2-2bef-46fb-b120-2712e3c56d81

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
theorem _root_.solution {σ : Type*} (F : MvPowerSeries σ ℂ_[p]) :
    IntegralMv F ↔ ∃ G : MvPowerSeries σ (intRing p), MvPowerSeries.map (intRing p).subtype G = F := by
  constructor
  · intro h
    refine ⟨fun e => ⟨MvPowerSeries.coeff e F, h e⟩, ?_⟩
    ext e
    rfl
  · rintro ⟨G, rfl⟩ e
    rw [MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff e G).2
end PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients
