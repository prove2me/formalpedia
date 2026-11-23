-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.sAdd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:18.719797+00:00
-- url     : https://prove2.me/submissions/f1fbe494-3a40-4801-8d71-8e87967605bc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_TendstoCoeffOfCont

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
variable (hE : CalcEquiv)
include hE
namespace PI.PhNormUnits.UnitaryGroupMassFormula
theorem _root_.solution {σ : Type} {f g h k : MvPowerSeries σ ℂ_[p]} (h1 : Simeq f g) (h2 : Simeq h k) :
    Simeq (f + h) (g + k) := (hE p σ f g h k).2.2.2.1 h1 h2
end PI.PhNormUnits.UnitaryGroupMassFormula
