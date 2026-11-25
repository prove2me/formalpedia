-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.norm_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:09:47.605345+00:00
-- url     : https://prove2.me/submissions/96edaa99-340f-41b7-959b-22bb51ac796a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_TendstoCoeffOfCont
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_SimeqSubst1
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_simeq_subst1
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_constantCoeff_formalSMul
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_constantCoeff_var
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_sb_C_mul
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_sb_X
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_sb_mulBy
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_sb_phAt


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
variable (hE : CalcEquiv) (hSub : CalcSubst)
variable {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
  (hinv : PowerSeries.subst ex l = PowerSeries.X)
include hSub hex0 hinv
namespace PI.PhNormUnits.UnitaryGroupMassFormula
theorem _root_.solution {ph : PowerSeries ℂ_[p]} (c N : ℂ_[p])
    (h : Simeq (phAt ph (mulBy l ex c (Xv ())) : MvPowerSeries Unit ℂ_[p]) (MvPowerSeries.C N * phAt ph (Xv ())))
    {τ : Type} (w : MvPowerSeries τ ℂ_[p]) (hw0 : MvPowerSeries.constantCoeff w = 0) (hw : IntegralMv w) :
    Simeq (phAt ph (mulBy l ex c w)) (MvPowerSeries.C N * phAt ph w) := by
  have hs : ∀ i : Unit, MvPowerSeries.constantCoeff ((fun _ : Unit => w) i) = 0 := fun _ => hw0
  have hv : MvPowerSeries.constantCoeff (PI.PhNormUnits.Xv () : MvPowerSeries Unit ℂ_[p]) = 0 := constantCoeff_var ()
  have hsm : MvPowerSeries.constantCoeff (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv () : MvPowerSeries Unit ℂ_[p])) = 0 :=
    constantCoeff_formalSMul hex0 hinv c _ hv
  have eL : MvPowerSeries.subst (fun _ : Unit => w)
      (PI.PhNormUnits.phAt ph (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv () : MvPowerSeries Unit ℂ_[p]))) = PI.PhNormUnits.phAt ph (PI.PhNormUnits.mulBy l ex c w) := by
    rw [sb_phAt (fun _ : Unit => w) hs ph _ hsm,
      sb_mulBy (fun _ : Unit => w) hs hex0 hinv c _ hv, sb_X (fun _ : Unit => w) hs ()]
  have eR : MvPowerSeries.subst (fun _ : Unit => w)
      (MvPowerSeries.C N * PI.PhNormUnits.phAt ph (PI.PhNormUnits.Xv () : MvPowerSeries Unit ℂ_[p])) = MvPowerSeries.C N * PI.PhNormUnits.phAt ph w := by
    rw [sb_C_mul (fun _ : Unit => w) hs N, sb_phAt (fun _ : Unit => w) hs ph _ hv,
      sb_X (fun _ : Unit => w) hs ()]
  have key := simeq_subst1 hSub hex0 hinv w hw0 hw h
  rw [eL, eR] at key
  exact key
end PI.PhNormUnits.UnitaryGroupMassFormula
