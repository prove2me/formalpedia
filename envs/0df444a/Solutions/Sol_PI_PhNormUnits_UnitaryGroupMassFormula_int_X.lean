-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.int_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:27.328625+00:00
-- url     : https://prove2.me/submissions/bc47a6ad-abef-4151-bedd-6c8cef8f8678

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
namespace PI.PhNormUnits.UnitaryGroupMassFormula
theorem _root_.solution {σ : Type*} (i : σ) : IntegralMv (Xv i : MvPowerSeries σ ℂ_[p]) := by
  intro n
  unfold IsIntP
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp
end PI.PhNormUnits.UnitaryGroupMassFormula
