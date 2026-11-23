-- Prove2me | solution 1 for P2M_PI_PhNormUnits_UnitaryGroupMassFormula_mulBy_zero__192bfb31d944
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:12.871588+00:00
-- url     : https://prove2.me/submissions/37c4c507-ed39-4533-9f8b-037d6eafd696

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.PhNormUnits PI.PhNormUnits.UnitaryGroupMassFormula
open PI.PhNormUnits
variable {p : ℕ} [Fact p.Prime]
variable {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
  (hinv : PowerSeries.subst ex l = PowerSeries.X)
variable {τ : Type*}
include hex0 hinv
omit hinv
namespace PI.PhNormUnits.UnitaryGroupMassFormula
theorem _root_.solution (a : MvPowerSeries τ ℂ_[p]) : mulBy l ex 0 a = 0 := by
  unfold mulBy
  rw [map_zero, zero_mul, PowerSeries.subst_zero_of_constantCoeff_zero hex0]
end PI.PhNormUnits.UnitaryGroupMassFormula
