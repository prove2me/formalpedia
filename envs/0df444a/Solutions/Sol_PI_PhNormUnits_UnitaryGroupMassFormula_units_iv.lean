-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.units_iv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:25:23.321428+00:00
-- url     : https://prove2.me/submissions/ebb0643d-8085-4186-9415-d6266ff54277

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_TendstoCoeffOfCont
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_SimeqSubst1
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_simeq_subst2
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_constantCoeff_formalSMul
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_constantCoeff_var
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_int_X
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_mulBy_mulBy
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_mulBy_one
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_sb_X
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_sb_be
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_sb_mulBy


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
include hE hSub hex0 hinv
namespace PI.PhNormUnits.UnitaryGroupMassFormula
theorem _root_.solution (c d : ℂ_[p]) (hc : c ≠ 0)
    (hw : IntegralMv (mulBy l ex c⁻¹ (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]))
    (h : Simeq (be l ex ph (mulBy l ex c (Xv 0)) (mulBy l ex c (Xv 1)) : MvPowerSeries (Fin 2) ℂ_[p])
      (be l ex ph (Xv 0) (mulBy l ex d (mulBy l ex c (Xv 1))))) :
    Simeq (be l ex ph (mulBy l ex c (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (be l ex ph (Xv 0) (mulBy l ex d (Xv 1))) := by
  have h0 : MvPowerSeries.constantCoeff (PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := constantCoeff_var 0
  have h1 : MvPowerSeries.constantCoeff (PI.PhNormUnits.Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := constantCoeff_var 1
  have hy0 : MvPowerSeries.constantCoeff (PI.PhNormUnits.mulBy l ex c⁻¹ (PI.PhNormUnits.Xv 1 : MvPowerSeries (Fin 2) ℂ_[p])) = 0 :=
    constantCoeff_formalSMul hex0 hinv _ _ h1
  have hcs0 : MvPowerSeries.constantCoeff (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p])) = 0 :=
    constantCoeff_formalSMul hex0 hinv _ _ h0
  have hcs1 : MvPowerSeries.constantCoeff (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv 1 : MvPowerSeries (Fin 2) ℂ_[p])) = 0 :=
    constantCoeff_formalSMul hex0 hinv _ _ h1
  have hdc1 : MvPowerSeries.constantCoeff
      (PI.PhNormUnits.mulBy l ex d (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]))) = 0 :=
    constantCoeff_formalSMul hex0 hinv _ _ hcs1
  have hs : ∀ i, MvPowerSeries.constantCoeff (![(PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]), PI.PhNormUnits.mulBy l ex c⁻¹ (PI.PhNormUnits.Xv 1)] i) = 0 := by
    intro i; fin_cases i
    · simp
    · simpa using hy0
  have hs0 : MvPowerSeries.subst ![(PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]), PI.PhNormUnits.mulBy l ex c⁻¹ (PI.PhNormUnits.Xv 1)] (PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) = PI.PhNormUnits.Xv 0 := by
    rw [sb_X _ hs 0]; simp
  have hs1 : MvPowerSeries.subst ![(PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]), PI.PhNormUnits.mulBy l ex c⁻¹ (PI.PhNormUnits.Xv 1)] (PI.PhNormUnits.Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) =
      PI.PhNormUnits.mulBy l ex c⁻¹ (PI.PhNormUnits.Xv 1) := by
    rw [sb_X _ hs 1]; simp
  have hcc : PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.mulBy l ex c⁻¹ (PI.PhNormUnits.Xv 1 : MvPowerSeries (Fin 2) ℂ_[p])) = PI.PhNormUnits.Xv 1 := by
    rw [mulBy_mulBy hex0 hinv c c⁻¹ _ h1, mul_inv_cancel₀ hc, mulBy_one hex0 hinv _ h1]
  have eL : MvPowerSeries.subst ![(PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]), PI.PhNormUnits.mulBy l ex c⁻¹ (PI.PhNormUnits.Xv 1)]
      (PI.PhNormUnits.be l ex ph (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p])) (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv 1))) =
      PI.PhNormUnits.be l ex ph (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv 0)) (PI.PhNormUnits.Xv 1) := by
    rw [sb_be _ hs hex0 hinv ph _ _ hcs0 hcs1, sb_mulBy _ hs hex0 hinv c _ h0,
      sb_mulBy _ hs hex0 hinv c _ h1, hs0, hs1, hcc]
  have eR : MvPowerSeries.subst ![(PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]), PI.PhNormUnits.mulBy l ex c⁻¹ (PI.PhNormUnits.Xv 1)]
      (PI.PhNormUnits.be l ex ph (PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) (PI.PhNormUnits.mulBy l ex d (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv 1)))) =
      PI.PhNormUnits.be l ex ph (PI.PhNormUnits.Xv 0) (PI.PhNormUnits.mulBy l ex d (PI.PhNormUnits.Xv 1)) := by
    rw [sb_be _ hs hex0 hinv ph _ _ h0 hdc1, sb_mulBy _ hs hex0 hinv d _ hcs1,
      sb_mulBy _ hs hex0 hinv c _ h1, hs0, hs1, hcc]
  have key := simeq_subst2 hSub hex0 hinv (PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p])
    (PI.PhNormUnits.mulBy l ex c⁻¹ (PI.PhNormUnits.Xv 1)) h0 hy0 (int_X 0) hw h
  rw [eL, eR] at key
  exact key
end PI.PhNormUnits.UnitaryGroupMassFormula
