-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.L_E
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:33.522803+00:00
-- url     : https://prove2.me/submissions/214e0957-4d29-4bde-ab61-4db6e07b632a

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
namespace PI.PhNormUnits.UnitaryGroupMassFormula
theorem _root_.solution (b : MvPowerSeries τ ℂ_[p]) (hb : MvPowerSeries.constantCoeff b = 0) :
    PowerSeries.subst (PowerSeries.subst b ex) l = b := by
  have hs : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex0
  have hb' : PowerSeries.HasSubst b := PowerSeries.HasSubst.of_constantCoeff_zero hb
  rw [← PowerSeries.subst_comp_subst_apply hs hb', hinv, PowerSeries.subst_X hb']
end PI.PhNormUnits.UnitaryGroupMassFormula
