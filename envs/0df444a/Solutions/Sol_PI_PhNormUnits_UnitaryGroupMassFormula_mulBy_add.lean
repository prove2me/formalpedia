-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.mulBy_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:13:29.511926+00:00
-- url     : https://prove2.me/submissions/4d936b69-3d7c-4992-a71a-6508d6f47efd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_L_E
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_constantCoeff_subst_log
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_L_add

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
theorem _root_.solution (c : ℂ_[p]) (a b : MvPowerSeries τ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) :
    mulBy l ex c (add l ex a b) = add l ex (mulBy l ex c a) (mulBy l ex c b) := by
  unfold mulBy
  rw [L_add hex0 hinv a b ha hb]
  unfold add
  rw [L_E hex0 hinv _ (by rw [map_mul, constantCoeff_subst_log hex0 hinv a ha, mul_zero]),
    L_E hex0 hinv _ (by rw [map_mul, constantCoeff_subst_log hex0 hinv b hb, mul_zero]), mul_add]
end PI.PhNormUnits.UnitaryGroupMassFormula
