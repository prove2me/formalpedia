-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.stepTrace_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:58:56.472597+00:00
-- url     : https://prove2.me/submissions/05be4957-a1d2-4dc7-a5b5-3d4142e47bac

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_TendstoCoeffOfCont
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_SimeqSubst1
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_StepUnitsOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_TraceAt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_NormUnitsSubstitution
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_NormUnitsOfCalculation
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_constantCoeff_var
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_int_X
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_norm_two_of
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_ph_const_of
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_trace_at
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_zc_inv_of
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_zc_two


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
theorem _root_.solution (hE : CalcEquiv) (hSub : CalcSubst) (hC : CalcClosed) (hD : NatDense)
    (hZ : CalcZpScale) : StepTrace := by
  intro p _ l ex ph S hH hA δ hδ
  obtain ⟨hex0, hinv, hp2, h22, hswap, -, -, hintS, hIA, htr, -, -, hB, hunit⟩ := hH
  have hU2 := hunit ((2 : ℂ_[p]), (2 : ℂ_[p])) h22 (norm_two_of hp2) (norm_two_of hp2)
  have hph := ph_const_of hU2 hex0 hinv
  obtain ⟨t, ht⟩ := htr δ hδ
  have h2inv : ∃ h : ℤ_[p], 2 * zc h = 1 := by
    obtain ⟨h, hh⟩ := zc_inv_of (2 : ℤ_[p]) (by rw [zc_two]; exact norm_two_of hp2)
    exact ⟨h, by rwa [zc_two] at hh⟩
  exact trace_at hE hSub hC hD hZ hex0 hinv hph hIA hB δ.1 δ.2 (hintS δ hδ) (hintS δ.swap (hswap δ hδ)) t ht
    (hA δ hδ) hU2 h2inv (Xv ()) (constantCoeff_var ()) (int_X ())
end PI.PhNormUnits.UnitaryGroupMassFormula
