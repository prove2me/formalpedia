-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.simeq_subst2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:48:51.316746+00:00
-- url     : https://prove2.me/submissions/fb163fb9-17de-4f3a-8960-b0b4ff803ca7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_TendstoCoeffOfCont
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_SimeqSubst1

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
theorem _root_.solution {τ : Type} (x y : MvPowerSeries τ ℂ_[p]) (hx0 : MvPowerSeries.constantCoeff x = 0)
    (hy0 : MvPowerSeries.constantCoeff y = 0) (hx : IntegralMv x) (hy : IntegralMv y)
    {f g : MvPowerSeries (Fin 2) ℂ_[p]} (h : Simeq f g) :
    Simeq (MvPowerSeries.subst ![x, y] f) (MvPowerSeries.subst ![x, y] g) := by
  have hs0 : ∀ i, MvPowerSeries.constantCoeff (![x, y] i) = 0 := by
    intro i; fin_cases i
    · simpa using hx0
    · simpa using hy0
  have hsI : ∀ i, PI.PhNormUnits.IntegralMv (![x, y] i) := by
    intro i; fin_cases i
    · simpa using hx
    · simpa using hy
  exact (hSub p (Fin 2) τ ![x, y] hs0 hsI).1 f g h
end PI.PhNormUnits.UnitaryGroupMassFormula
