-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.coeff_expMv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:19.211464+00:00
-- url     : https://prove2.me/submissions/ab4e8db3-ee4f-4e74-9a3e-eebf67a9e979

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
theorem _root_.solution {σ : Type*} (F : MvPowerSeries σ ℂ_[p]) (α : σ →₀ ℕ) :
    MvPowerSeries.coeff α (expMv F) =
      ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1), MvPowerSeries.coeff α (F ^ n) / (n.factorial : ℂ_[p]) :=
  rfl
end PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients
