-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.be_add_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:32:50.023667+00:00
-- url     : https://prove2.me/submissions/ccf392b3-326f-49dd-94b1-6c55a869d171

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_TendstoCoeffOfCont
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffVar
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_constantCoeff_var
import Theorems.Thm_P2M_PI_PhNormUnits_UnitaryGroupMassFormula_sb_add__b34afe4daad2
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_constantCoeff_formalAdd
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_sb_X
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_sb_add
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_sb_be


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
include hSub hex0 hinv hB
namespace PI.PhNormUnits.UnitaryGroupMassFormula
theorem _root_.solution {τ : Type} (x y z : MvPowerSeries τ ℂ_[p]) (hx0 : MvPowerSeries.constantCoeff x = 0)
    (hy0 : MvPowerSeries.constantCoeff y = 0) (hz0 : MvPowerSeries.constantCoeff z = 0)
    (hx : IntegralMv x) (hy : IntegralMv y) (hz : IntegralMv z) :
    Simeq (be l ex ph (add l ex x y) z) (be l ex ph x z + be l ex ph y z) := by

  have hs0 : ∀ i, MvPowerSeries.constantCoeff (![x, y, z] i) = 0 := by
    intro i
    fin_cases i <;> simp [hx0, hy0, hz0]
  have hsI : ∀ i, IntegralMv (![x, y, z] i) := by
    intro i
    fin_cases i <;> simp [hx, hy, hz]
  have hA01 : MvPowerSeries.constantCoeff (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 :=
    constantCoeff_formalAdd hex0 hinv _ _ (constantCoeff_var 0) (constantCoeff_var 1)
  have h1 := (hSub p (Fin 3) τ ![x, y, z] hs0 hsI).1 _ _ hB
  rw [sb_be ![x, y, z] hs0 hex0 hinv ph _ _ hA01 (constantCoeff_var 2), sb_add ![x, y, z] hs0 hex0 hinv _ _ (constantCoeff_var 0) (constantCoeff_var 1),
    sb_add', sb_be ![x, y, z] hs0 hex0 hinv ph _ _ (constantCoeff_var 0) (constantCoeff_var 2),
    sb_be ![x, y, z] hs0 hex0 hinv ph _ _ (constantCoeff_var 1) (constantCoeff_var 2), sb_X, sb_X, sb_X] at h1
  · exact h1
  all_goals first | exact hs0 | exact hex0 | exact hinv
end PI.PhNormUnits.UnitaryGroupMassFormula
