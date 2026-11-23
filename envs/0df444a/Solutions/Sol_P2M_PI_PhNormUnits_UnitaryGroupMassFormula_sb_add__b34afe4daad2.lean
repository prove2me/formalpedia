-- Prove2me | solution 1 for P2M_PI_PhNormUnits_UnitaryGroupMassFormula_sb_add__b34afe4daad2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:27.363241+00:00
-- url     : https://prove2.me/submissions/08e83b6d-63f8-4a78-b337-2b520a985983

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
theorem _root_.solution (F G : MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries.subst s (F + G) = MvPowerSeries.subst s F + MvPowerSeries.subst s G :=
  MvPowerSeries.subst_add (MvPowerSeries.hasSubst_of_constantCoeff_zero hs) F G
end PI.PhNormUnits.UnitaryGroupMassFormula
