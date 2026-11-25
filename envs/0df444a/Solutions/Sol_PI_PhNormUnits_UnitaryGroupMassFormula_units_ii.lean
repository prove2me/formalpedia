-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.units_ii
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:48:55.347484+00:00
-- url     : https://prove2.me/submissions/50977877-4249-4ef6-8c95-9b2ec2d60a60

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_TendstoCoeffOfCont
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_SimeqSubst1
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_be_zp
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_constantCoeff_var
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_int_X
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_mulBy_mulBy
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_sSymm


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
variable (hE : CalcEquiv) (hSub : CalcSubst) (hC : CalcClosed) (hD : NatDense)
variable {l ex ph : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
  (hinv : PowerSeries.subst ex l = PowerSeries.X) (hph : PowerSeries.constantCoeff ph = 0)
  (hIA : IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]))
  (hB : Simeq (be l ex ph (add l ex (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (be l ex ph (Xv 0) (Xv 2) + be l ex ph (Xv 1) (Xv 2)))
include hE hSub hC hD hex0 hinv hph hIA hB
namespace PI.PhNormUnits.UnitaryGroupMassFormula
theorem _root_.solution (c d : ℂ_[p]) (n : ℤ_[p]) (hn : c * d = zc n) :
    Simeq (MvPowerSeries.C (c * d) * be l ex ph (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (be l ex ph (Xv 0) (mulBy l ex d (mulBy l ex c (Xv 1)))) := by
  have h0 : MvPowerSeries.constantCoeff (PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := constantCoeff_var 0
  have h1 : MvPowerSeries.constantCoeff (PI.PhNormUnits.Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := constantCoeff_var 1
  have hcomp : PI.PhNormUnits.mulBy l ex d (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv 1 : MvPowerSeries (Fin 2) ℂ_[p])) =
      PI.PhNormUnits.mulBy l ex (PI.PhNormUnits.zc n) (PI.PhNormUnits.Xv 1) := by
    rw [mulBy_mulBy hex0 hinv d c _ h1, mul_comm d c, hn]
  have key := be_zp hE hSub hex0 hinv hB hC hD hph hIA
    (PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) (PI.PhNormUnits.Xv 1) h0 h1 (int_X 0) (int_X 1) n
  rw [hcomp, hn]
  exact sSymm hE key
end PI.PhNormUnits.UnitaryGroupMassFormula
