-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.z0_pt_zero_pt_one_L3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:07.199804+00:00
-- url     : https://prove2.me/submissions/28e4523f-0ace-4878-8a48-38e302cb2040

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
variable {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
  (hinv : PowerSeries.subst ex l = PowerSeries.X)
variable {τ : Type*}
include hex0 hinv
omit hinv
namespace PI.PhNormUnits.UnitaryGroupMassFormula
theorem _root_.solution (b : MvPowerSeries τ ℂ_[p]) (hb : MvPowerSeries.constantCoeff b = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst b ex) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hb ex hex0
end PI.PhNormUnits.UnitaryGroupMassFormula
