-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.sum_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:04:25.232133+00:00
-- url     : https://prove2.me/submissions/fec8bf9e-b531-4755-bcc8-2b090b83e8cf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_TendstoCoeffOfCont
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_SimeqSubst1
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_StepUnitsOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_TraceAt
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_add_mulBy
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_constantCoeff_formalSMul
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_constantCoeff_var
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_int_X
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_mulBy_mulBy
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_sAdd
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_sOfEq
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_sTrans
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_sb_X
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_sb_be
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_sb_mulBy
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_simeq_subst2


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
variable (hE : CalcEquiv) (hSub : CalcSubst) (hC : CalcClosed) (hD : NatDense) (hZ : CalcZpScale)
variable {l ex ph : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
  (hinv : PowerSeries.subst ex l = PowerSeries.X) (hph : PowerSeries.constantCoeff ph = 0)
  (hIA : IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]))
  (hB : Simeq (be l ex ph (add l ex (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (be l ex ph (Xv 0) (Xv 2) + be l ex ph (Xv 1) (Xv 2)))
include hE hSub hex0 hinv
namespace PI.PhNormUnits.UnitaryGroupMassFormula
theorem _root_.solution (β γ : ℂ_[p] × ℂ_[p]) (iγ : IntegralMv (mulBy l ex γ.1 (Xv ()) : MvPowerSeries Unit ℂ_[p]))
    (hsw : Simeq (be l ex ph (mulBy l ex β.1 (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (be l ex ph (Xv 0) (mulBy l ex β.2 (Xv 1))))
    (htr : Simeq (be l ex ph (Xv ()) (mulBy l ex (β.2 * γ.1) (Xv ())) : MvPowerSeries Unit ℂ_[p])
      (MvPowerSeries.C (β.2 * γ.1 + β.1 * γ.2) * phAt ph (Xv ())))
    (nβ : Simeq (phAt ph (mulBy l ex β.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
      (MvPowerSeries.C (β.1 * β.2) * phAt ph (Xv ())))
    (nγ : Simeq (phAt ph (mulBy l ex γ.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
      (MvPowerSeries.C (γ.1 * γ.2) * phAt ph (Xv ()))) :
    Simeq (phAt ph (mulBy l ex (β.1 + γ.1) (Xv ())) : MvPowerSeries Unit ℂ_[p])
      (MvPowerSeries.C ((β.1 + γ.1) * (β.2 + γ.2)) * phAt ph (Xv ())) := by
  have hX0 : MvPowerSeries.constantCoeff (Xv () : MvPowerSeries Unit ℂ_[p]) = 0 := constantCoeff_var ()
  have hg0 : MvPowerSeries.constantCoeff (mulBy l ex γ.1 (Xv ()) : MvPowerSeries Unit ℂ_[p]) = 0 :=
    constantCoeff_formalSMul hex0 hinv γ.1 _ hX0
  have hb0 : MvPowerSeries.constantCoeff (mulBy l ex β.1 (Xv ()) : MvPowerSeries Unit ℂ_[p]) = 0 :=
    constantCoeff_formalSMul hex0 hinv β.1 _ hX0
  have hs2 : ∀ i, MvPowerSeries.constantCoeff
      (![Xv (), mulBy l ex γ.1 (Xv ())] i : MvPowerSeries Unit ℂ_[p]) = 0 := by
    intro i; fin_cases i
    · simp [hX0]
    · simpa using hg0
  have S1 : Simeq (be l ex ph (mulBy l ex β.1 (Xv ())) (mulBy l ex γ.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
      (be l ex ph (Xv ()) (mulBy l ex (β.2 * γ.1) (Xv ()))) := by
    have e := simeq_subst2 hSub hex0 hinv (Xv ()) (mulBy l ex γ.1 (Xv ())) hX0 hg0 (int_X ()) iγ hsw
    rw [sb_be _ hs2 hex0 hinv ph _ _ (constantCoeff_formalSMul hex0 hinv β.1 _ (constantCoeff_var 0)) (constantCoeff_var 1),
      sb_be _ hs2 hex0 hinv ph _ _ (constantCoeff_var 0) (constantCoeff_formalSMul hex0 hinv β.2 _ (constantCoeff_var 1)),
      sb_mulBy _ hs2 hex0 hinv β.1 _ (constantCoeff_var 0), sb_mulBy _ hs2 hex0 hinv β.2 _ (constantCoeff_var 1),
      sb_X _ hs2, sb_X _ hs2] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e
    rwa [mulBy_mulBy hex0 hinv β.2 γ.1 _ hX0] at e
  have e : phAt ph (mulBy l ex (β.1 + γ.1) (Xv ())) =
      be l ex ph (mulBy l ex β.1 (Xv ())) (mulBy l ex γ.1 (Xv ())) +
        phAt ph (mulBy l ex β.1 (Xv ())) + phAt ph (mulBy l ex γ.1 (Xv ())) := by
    rw [be, add_mulBy hex0 hinv β.1 γ.1 _ hX0]
    ring
  rw [e]
  refine sTrans hE (sAdd hE (sAdd hE (sTrans hE S1 htr) nβ) nγ) (sOfEq hE ?_)
  simp only [map_add, map_mul]
  ring
end PI.PhNormUnits.UnitaryGroupMassFormula
