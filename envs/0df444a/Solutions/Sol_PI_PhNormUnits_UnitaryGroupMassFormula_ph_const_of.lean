-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.ph_const_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:09:36.223094+00:00
-- url     : https://prove2.me/submissions/6022032c-f50b-497b-b4b9-79c39518bda3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_TendstoCoeffOfCont
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffVar
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_constantCoeff_var
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_const_phAt
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
open Classical Filter Topology MvPowerSeries.WithPiTopology
open PI PI.PhNormUnits PI.PhNormUnits.UnitaryGroupMassFormula
open PI.PhNormUnits
variable {p : ℕ} [Fact p.Prime]
variable (hE : CalcEquiv) (hSub : CalcSubst)
variable {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
  (hinv : PowerSeries.subst ex l = PowerSeries.X)
namespace PI.PhNormUnits.UnitaryGroupMassFormula
theorem _root_.solution {ph : PowerSeries ℂ_[p]}
    (h2 : Simeq (phAt ph (mulBy l ex 2 (Xv ())) : MvPowerSeries Unit ℂ_[p])
      (MvPowerSeries.C (2 * 2) * phAt ph (Xv ()))) (hex0 : PowerSeries.constantCoeff ex = 0)
    (hinv : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.constantCoeff ph = 0 := by

  have hm0 : MvPowerSeries.constantCoeff (mulBy l ex 2 (Xv () : MvPowerSeries Unit ℂ_[p])) = 0 := by
    unfold mulBy
    refine z0_pt_zero_pt_one_L3 hex0 _ ?_
    rw [map_mul, constantCoeff_subst_log hex0 hinv _ (constantCoeff_var ()), mul_zero]
  have hc1 : MvPowerSeries.constantCoeff (phAt ph (mulBy l ex 2 (Xv ())) : MvPowerSeries Unit ℂ_[p]) =
      PowerSeries.constantCoeff ph := const_phAt ph _ hm0
  have hc2 : MvPowerSeries.constantCoeff (phAt ph (Xv ()) : MvPowerSeries Unit ℂ_[p]) =
      PowerSeries.constantCoeff ph := const_phAt ph _ (constantCoeff_var ())
  have hc3 : MvPowerSeries.constantCoeff (MvPowerSeries.C (2 * 2 : ℂ_[p]) : MvPowerSeries Unit ℂ_[p]) = 2 * 2 :=
    MvPowerSeries.constantCoeff_C _
  have h1 := h2.1
  rw [map_sub, map_mul, hc1, hc2, hc3] at h1
  have h3 : (3 : ℂ_[p]) ≠ 0 := by norm_num
  have h4 : 3 * PowerSeries.constantCoeff ph = 0 := by linear_combination -h1
  rcases mul_eq_zero.mp h4 with h | h
  · exact absurd h h3
  · exact h
end PI.PhNormUnits.UnitaryGroupMassFormula
