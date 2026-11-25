-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.stepAll_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:04:21.95434+00:00
-- url     : https://prove2.me/submissions/46c9b846-928d-471d-b702-1e97beaf15de

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_TendstoCoeffOfCont
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_SimeqSubst1
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_StepUnitsOf
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_add_mulBy
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_be_add_left
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_be_add_right
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_constantCoeff_formalSMul
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_constantCoeff_var
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_int_X
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_int_mulBy_of
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_sAdd
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_sSymm
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_sTrans


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
theorem _root_.solution (hE : CalcEquiv) (hSub : CalcSubst) : StepAll := by
  intro p _ l ex ph S hS hU α hα
  obtain ⟨hex0, hinv, -, -, hswap, -, -, hint_r, hIA, -, -, hdec, hB, -⟩ := hS
  obtain ⟨β, hβ, γ, hγ, hb1, hb2, hg1, hg2, rfl⟩ := hdec α hα
  have h0 : MvPowerSeries.constantCoeff (PI.PhNormUnits.Xv (0 : Fin 2) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 :=
    constantCoeff_var _
  have h1 : MvPowerSeries.constantCoeff (PI.PhNormUnits.Xv (1 : Fin 2) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 :=
    constantCoeff_var _
  have i0 : PI.PhNormUnits.IntegralMv (PI.PhNormUnits.Xv (0 : Fin 2) : MvPowerSeries (Fin 2) ℂ_[p]) := int_X _
  have i1 : PI.PhNormUnits.IntegralMv (PI.PhNormUnits.Xv (1 : Fin 2) : MvPowerSeries (Fin 2) ℂ_[p]) := int_X _
  have hI1 : ∀ δ ∈ S, ∀ x : MvPowerSeries (Fin 2) ℂ_[p], MvPowerSeries.constantCoeff x = 0 →
      PI.PhNormUnits.IntegralMv x → PI.PhNormUnits.IntegralMv (PI.PhNormUnits.mulBy l ex δ.1 x) :=
    fun δ hδ x hx0 hx => int_mulBy_of hSub hex0 hinv δ.1 (hint_r δ hδ) x hx0 hx
  have hI2 : ∀ δ ∈ S, ∀ x : MvPowerSeries (Fin 2) ℂ_[p], MvPowerSeries.constantCoeff x = 0 →
      PI.PhNormUnits.IntegralMv x → PI.PhNormUnits.IntegralMv (PI.PhNormUnits.mulBy l ex δ.2 x) :=
    fun δ hδ x hx0 hx => by
      have h := hint_r _ (hswap δ hδ)
      rw [Prod.fst_swap] at h
      exact int_mulBy_of hSub hex0 hinv δ.2 h x hx0 hx
  have c0 : ∀ (c : ℂ_[p]) (x : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.constantCoeff x = 0 →
      MvPowerSeries.constantCoeff (PI.PhNormUnits.mulBy l ex c x) = 0 :=
    fun c x hx => constantCoeff_formalSMul hex0 hinv c x hx
  show PI.PhNormUnits.Simeq (PI.PhNormUnits.be l ex ph (PI.PhNormUnits.mulBy l ex (β.1 + γ.1) (PI.PhNormUnits.Xv 0)) (PI.PhNormUnits.Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
    (PI.PhNormUnits.be l ex ph (PI.PhNormUnits.Xv 0) (PI.PhNormUnits.mulBy l ex (β.2 + γ.2) (PI.PhNormUnits.Xv 1)))
  rw [← add_mulBy hex0 hinv β.1 γ.1 _ h0,
    ← add_mulBy hex0 hinv β.2 γ.2 _ h1]
  have L := be_add_left hSub hex0 hinv hB (PI.PhNormUnits.mulBy l ex β.1 (PI.PhNormUnits.Xv 0))
    (PI.PhNormUnits.mulBy l ex γ.1 (PI.PhNormUnits.Xv 0)) (PI.PhNormUnits.Xv 1) (c0 _ _ h0) (c0 _ _ h0) h1
    (hI1 β hβ _ h0 i0) (hI1 γ hγ _ h0 i0) i1
  have R := be_add_right hSub hex0 hinv hB (PI.PhNormUnits.mulBy l ex β.2 (PI.PhNormUnits.Xv 1))
    (PI.PhNormUnits.mulBy l ex γ.2 (PI.PhNormUnits.Xv 1)) (PI.PhNormUnits.Xv 0) (c0 _ _ h1) (c0 _ _ h1) h0
    (hI2 β hβ _ h1 i1) (hI2 γ hγ _ h1 i1) i0
  exact sTrans hE L (sTrans hE
    (sAdd hE (hU β hβ hb1 hb2) (hU γ hγ hg1 hg2)) (sSymm hE R))
end PI.PhNormUnits.UnitaryGroupMassFormula
