-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.mulBy_mulBy
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:26.523819+00:00
-- url     : https://prove2.me/submissions/cbb0a132-7897-49b2-a6a8-6e0be9e3a3de

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_L_mulBy

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
namespace PI.PhNormUnits.UnitaryGroupMassFormula
theorem _root_.solution (c d : ℂ_[p]) (a : MvPowerSeries τ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0) :
    mulBy l ex c (mulBy l ex d a) = mulBy l ex (c * d) a := by
  show PowerSeries.subst (MvPowerSeries.C c * PowerSeries.subst (mulBy l ex d a) l) ex = _
  rw [L_mulBy hex0 hinv d a ha, ← mul_assoc, ← map_mul]
  rfl
end PI.PhNormUnits.UnitaryGroupMassFormula
