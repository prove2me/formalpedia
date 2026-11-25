-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.int_mulBy_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:31:06.861094+00:00
-- url     : https://prove2.me/submissions/23c73a08-2828-431e-a370-43cb57c79eb4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_TendstoCoeffOfCont
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffVar
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_int_add
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
include hSub hex0 hinv
namespace PI.PhNormUnits.UnitaryGroupMassFormula
theorem _root_.solution (hIA : IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])) {τ : Type}
    (x : MvPowerSeries τ ℂ_[p]) (hx0 : MvPowerSeries.constantCoeff x = 0) (hx : IntegralMv x) (k : ℕ) :
    IntegralMv (mulBy l ex (k : ℂ_[p]) x) := by

  have hz : ∀ c, MvPowerSeries.constantCoeff (mulBy l ex c x) = 0 := by
    intro c
    unfold mulBy
    refine z0_pt_zero_pt_one_L3 hex0 _ ?_
    rw [map_mul, constantCoeff_subst_log hex0 hinv x hx0, mul_zero]
  induction k with
  | zero =>
    rw [Nat.cast_zero, mulBy_zero' hex0]
    intro n
    simp [IsIntP]
  | succ k ih =>
    rw [mulBy_succ hex0 hinv k x hx0]
    exact int_add hSub hex0 hinv hIA _ _ (hz _) hx0 ih hx
end PI.PhNormUnits.UnitaryGroupMassFormula
