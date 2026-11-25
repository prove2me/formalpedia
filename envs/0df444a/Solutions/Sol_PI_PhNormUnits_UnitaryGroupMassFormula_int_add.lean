-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.int_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:04:02.681617+00:00
-- url     : https://prove2.me/submissions/8345d7ea-e461-4d50-9f33-93ef1a402760

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_TendstoCoeffOfCont
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffVar
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_constantCoeff_var
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_sb_X
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_sb_add


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
    (x y : MvPowerSeries τ ℂ_[p]) (hx0 : MvPowerSeries.constantCoeff x = 0)
    (hy0 : MvPowerSeries.constantCoeff y = 0) (hx : IntegralMv x) (hy : IntegralMv y) :
    IntegralMv (add l ex x y) := by

  have hs0 : ∀ i, MvPowerSeries.constantCoeff (![x, y] i) = 0 := by
    intro i
    fin_cases i <;> simp [hx0, hy0]
  have hsI : ∀ i, IntegralMv (![x, y] i) := by
    intro i
    fin_cases i <;> simp [hx, hy]
  have h1 := (hSub p (Fin 2) τ ![x, y] hs0 hsI).2 _ hIA
  rw [sb_add ![x, y] hs0 hex0 hinv _ _ (constantCoeff_var 0) (constantCoeff_var 1), sb_X, sb_X] at h1
  · exact h1
  all_goals exact hs0
end PI.PhNormUnits.UnitaryGroupMassFormula
