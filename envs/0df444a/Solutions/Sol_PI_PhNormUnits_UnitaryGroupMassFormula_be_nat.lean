-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.be_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:35:59.86099+00:00
-- url     : https://prove2.me/submissions/0ca29802-c52b-4978-860e-f83402d2f836

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_TendstoCoeffOfCont
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffVar
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_int_mulBy_nat
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_be_zero
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_be_add_right
import Theorems.Thm_P2M_PI_PhNormUnits_UnitaryGroupMassFormula_mulBy_zero__192bfb31d944
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_constantCoeff_subst_log
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_mulBy_succ
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
variable {ph : PowerSeries ℂ_[p]}
  (hB : Simeq (be l ex ph (add l ex (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (be l ex ph (Xv 0) (Xv 2) + be l ex ph (Xv 1) (Xv 2)))
include hE hSub hex0 hinv hB
namespace PI.PhNormUnits.UnitaryGroupMassFormula
theorem _root_.solution (hph : PowerSeries.constantCoeff ph = 0)
    (hIA : IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])) {τ : Type}
    (z y : MvPowerSeries τ ℂ_[p]) (hz0 : MvPowerSeries.constantCoeff z = 0)
    (hy0 : MvPowerSeries.constantCoeff y = 0) (hz : IntegralMv z) (hy : IntegralMv y) (k : ℕ) :
    Simeq (be l ex ph z (mulBy l ex (k : ℂ_[p]) y)) (MvPowerSeries.C (k : ℂ_[p]) * be l ex ph z y) := by

  induction k with
  | zero =>
    rw [Nat.cast_zero, mulBy_zero' hex0, be_zero hex0 hinv hph z hz0, map_zero, zero_mul]
    exact (hE p τ 0 0 0 0).1
  | succ k ih =>
    rw [mulBy_succ hex0 hinv k y hy0]
    have hmk0 : MvPowerSeries.constantCoeff (mulBy l ex (k : ℂ_[p]) y) = 0 := by
      unfold mulBy
      refine z0_pt_zero_pt_one_L3 hex0 _ ?_
      rw [map_mul, constantCoeff_subst_log hex0 hinv y hy0, mul_zero]
    have hmkI : IntegralMv (mulBy l ex (k : ℂ_[p]) y) := int_mulBy_nat hSub hex0 hinv hIA y hy0 hy k
    have h1 := be_add_right hSub hex0 hinv hB (mulBy l ex (k : ℂ_[p]) y) y z hmk0 hy0 hz0 hmkI hy hz
    have h2 := (hE p τ _ _ _ _).2.2.2.1 ih
      (hE p τ (be l ex ph z y) (be l ex ph z y) (be l ex ph z y) (be l ex ph z y)).1
    have h3 := (hE p τ _ _ _ 0).2.2.1 h1 h2
    have h4 : MvPowerSeries.C (k : ℂ_[p]) * be l ex ph z y + be l ex ph z y =
        MvPowerSeries.C ((k + 1 : ℕ) : ℂ_[p]) * be l ex ph z y := by
      rw [Nat.cast_succ, map_add, map_one]
      ring
    rw [← h4]
    exact h3
end PI.PhNormUnits.UnitaryGroupMassFormula
