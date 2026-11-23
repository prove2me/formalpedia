-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.constantCoeff_var
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:26.978093+00:00
-- url     : https://prove2.me/submissions/95b4f66f-e790-4852-a717-68b4479b9329

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_TendstoCoeffOfCont
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffVar

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
namespace PI.PhNormUnits.UnitaryGroupMassFormula
theorem _root_.solution {σ : Type*} (i : σ) : MvPowerSeries.constantCoeff (Xv i : MvPowerSeries σ ℂ_[p]) = 0 := MvPowerSeries.constantCoeff_X i
end PI.PhNormUnits.UnitaryGroupMassFormula
