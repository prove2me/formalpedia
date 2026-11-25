-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.stepUnits_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:56:43.253865+00:00
-- url     : https://prove2.me/submissions/0a3de3b5-06ba-48e4-b5fc-4cec13a3a1e1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_TendstoCoeffOfCont
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_SimeqSubst1
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_StepUnitsOf
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_constantCoeff_formalSMul
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_constantCoeff_var
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_int_X
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_int_mulBy_of
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_int_mulBy_zp
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_mulBy_mulBy
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_norm_two_of
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_ph_const_of
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_sTrans
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_units_i
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_units_ii
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_units_iv
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_zc_inv_of


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
namespace PI.PhNormUnits.UnitaryGroupMassFormula
theorem _root_.solution (hE : CalcEquiv) (hSub : CalcSubst) (hC : CalcClosed) (hD : NatDense) : StepUnits := by
  intro p _ l ex ph S hS α hα h1 h2
  obtain ⟨hex0, hinv, hp2, h22, hswap, -, -, hint_r, hIA, -, hprod, -, hB, hNorm⟩ := hS
  have hph : PowerSeries.constantCoeff ph = 0 := by
    have h2n : ‖(2 : ℂ_[p])‖ = 1 := norm_two_of hp2
    have h2' := hNorm ((2 : ℂ_[p]), (2 : ℂ_[p])) h22 h2n h2n
    dsimp only at h2'
    exact ph_const_of h2' hex0 hinv
  obtain ⟨n, hn⟩ := hprod α hα
  have hU := hNorm α hα h1 h2
  have hc : α.1 ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have hnorm : ‖PI.PhNormUnits.zc n‖ = 1 := by rw [← hn, norm_mul, h1, h2, one_mul]
  obtain ⟨m, hm⟩ := zc_inv_of n hnorm
  have hinvc : α.1⁻¹ = α.2 * PI.PhNormUnits.zc m := by
    apply inv_eq_of_mul_eq_one_right
    rw [← mul_assoc, hn, hm]
  have h1v : MvPowerSeries.constantCoeff (PI.PhNormUnits.Xv (1 : Fin 2) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 :=
    constantCoeff_var _
  have hd : PI.PhNormUnits.IntegralMv (PI.PhNormUnits.mulBy l ex α.2 (PI.PhNormUnits.Xv ()) : MvPowerSeries Unit ℂ_[p]) := by
    have h := hint_r _ (hswap α hα)
    rw [Prod.fst_swap] at h
    exact h
  have hw : PI.PhNormUnits.IntegralMv (PI.PhNormUnits.mulBy l ex α.1⁻¹ (PI.PhNormUnits.Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) := by
    rw [hinvc, ← mulBy_mulBy hex0 hinv α.2 (PI.PhNormUnits.zc m) (PI.PhNormUnits.Xv (1 : Fin 2)) h1v]
    exact int_mulBy_of hSub hex0 hinv α.2 hd _
      (constantCoeff_formalSMul hex0 hinv _ _ h1v)
      (int_mulBy_zp hSub hex0 hinv hC hD hIA _ h1v
        (int_X _) m)
  have step1 := units_i hE hSub hex0 hinv hIA α.1 (α.1 * α.2) hU
  have step2 := units_ii hE hSub hC hD hex0 hinv hph hIA hB α.1 α.2 n hn
  exact units_iv hE hSub hex0 hinv α.1 α.2 hc hw (sTrans hE step1 step2)
end PI.PhNormUnits.UnitaryGroupMassFormula
