-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.sb_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:07.173102+00:00
-- url     : https://prove2.me/submissions/7a88b769-218e-44be-b8e8-9ed28f85204d

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
theorem _root_.solution (i : σ) : MvPowerSeries.subst s (Xv i : MvPowerSeries σ ℂ_[p]) = s i :=
  MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hs) i
end PI.PhNormUnits.UnitaryGroupMassFormula
