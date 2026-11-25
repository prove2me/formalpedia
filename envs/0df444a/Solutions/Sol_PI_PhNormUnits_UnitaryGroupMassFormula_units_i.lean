-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.units_i
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:18:44.904246+00:00
-- url     : https://prove2.me/submissions/6f694f27-11fa-4b0e-bdd7-24e9116aa43c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_TendstoCoeffOfCont
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_SimeqSubst1
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_norm_at
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_constantCoeff_formalAdd
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_constantCoeff_var
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_int_X
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_mulBy_add
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_sSub


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
include hE hSub hex0 hinv hIA
namespace PI.PhNormUnits.UnitaryGroupMassFormula
theorem _root_.solution (c N : ℂ_[p])
    (hU : Simeq (phAt ph (mulBy l ex c (Xv ())) : MvPowerSeries Unit ℂ_[p]) (MvPowerSeries.C N * phAt ph (Xv ()))) :
    Simeq (be l ex ph (mulBy l ex c (Xv 0)) (mulBy l ex c (Xv 1)) : MvPowerSeries (Fin 2) ℂ_[p])
      (MvPowerSeries.C N * be l ex ph (Xv 0) (Xv 1)) := by
  have h0 : MvPowerSeries.constantCoeff (PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := constantCoeff_var 0
  have h1 : MvPowerSeries.constantCoeff (PI.PhNormUnits.Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := constantCoeff_var 1
  have hA := norm_at hSub hex0 hinv c N hU
    (PI.PhNormUnits.add l ex (PI.PhNormUnits.Xv 0) (PI.PhNormUnits.Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) (constantCoeff_formalAdd hex0 hinv _ _ h0 h1) hIA
  have hX := norm_at hSub hex0 hinv c N hU
    (PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) h0 (int_X 0)
  have hY := norm_at hSub hex0 hinv c N hU
    (PI.PhNormUnits.Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) h1 (int_X 1)
  have hsum := sSub hE (sSub hE hA hX) hY
  have eL : PI.PhNormUnits.be l ex ph (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p])) (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv 1)) =
      PI.PhNormUnits.phAt ph (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.add l ex (PI.PhNormUnits.Xv 0) (PI.PhNormUnits.Xv 1))) - PI.PhNormUnits.phAt ph (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv 0))
        - PI.PhNormUnits.phAt ph (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv 1)) := by
    rw [mulBy_add hex0 hinv c _ _ h0 h1]
    rfl
  have eR : MvPowerSeries.C N * PI.PhNormUnits.be l ex ph (PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) (PI.PhNormUnits.Xv 1) =
      MvPowerSeries.C N * PI.PhNormUnits.phAt ph (PI.PhNormUnits.add l ex (PI.PhNormUnits.Xv 0) (PI.PhNormUnits.Xv 1)) - MvPowerSeries.C N * PI.PhNormUnits.phAt ph (PI.PhNormUnits.Xv 0)
        - MvPowerSeries.C N * PI.PhNormUnits.phAt ph (PI.PhNormUnits.Xv 1) := by
    simp only [PI.PhNormUnits.be]
    ring
  rw [eL, eR]
  exact hsum
end PI.PhNormUnits.UnitaryGroupMassFormula
