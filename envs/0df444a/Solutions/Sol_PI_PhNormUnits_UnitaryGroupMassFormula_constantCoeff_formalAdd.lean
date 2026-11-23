-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.constantCoeff_formalAdd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:46:59.351109+00:00
-- url     : https://prove2.me/submissions/fdb9fd14-f0a3-462c-b1a9-4ab29fb8ced9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_constantCoeff_subst_log
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_z0_pt_zero_pt_one_L3

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
theorem _root_.solution (a b : MvPowerSeries τ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) : MvPowerSeries.constantCoeff (add l ex a b) = 0 := by
  unfold add
  apply z0_pt_zero_pt_one_L3 hex0
  rw [map_add, constantCoeff_subst_log hex0 hinv a ha, constantCoeff_subst_log hex0 hinv b hb, add_zero]
end PI.PhNormUnits.UnitaryGroupMassFormula
