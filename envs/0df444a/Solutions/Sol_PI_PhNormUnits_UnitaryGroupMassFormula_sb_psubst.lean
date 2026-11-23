-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.sb_psubst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:33.775411+00:00
-- url     : https://prove2.me/submissions/84f2a6f0-5626-4a93-a5d5-b6ab2d95c64b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul

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
variable {σ τ : Type*} [Finite σ] {l ex : PowerSeries ℂ_[p]} (s : σ → MvPowerSeries τ ℂ_[p])
  (hs : ∀ i, MvPowerSeries.constantCoeff (s i) = 0)
include hs
namespace PI.PhNormUnits.UnitaryGroupMassFormula
theorem _root_.solution (a : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (f : PowerSeries ℂ_[p]) :
    MvPowerSeries.subst s (PowerSeries.subst a f) = PowerSeries.subst (MvPowerSeries.subst s a) f := by
  have hS : MvPowerSeries.HasSubst s := MvPowerSeries.hasSubst_of_constantCoeff_zero hs
  have ha' : MvPowerSeries.HasSubst (fun _ : Unit => a) :=
    (PowerSeries.HasSubst.of_constantCoeff_zero ha).const
  rw [PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply ha' hS]
  rfl
end PI.PhNormUnits.UnitaryGroupMassFormula
