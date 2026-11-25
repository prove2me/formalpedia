-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.E_L
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:15:39.491268+00:00
-- url     : https://prove2.me/submissions/745a2542-a6eb-4c1f-9e06-6384c48dcbb9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_l_const
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_ex_l

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
theorem _root_.solution (a : MvPowerSeries τ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0) :
    PowerSeries.subst (PowerSeries.subst a l) ex = a := by
  have hl0 := l_const hex0 hinv
  have hs : PowerSeries.HasSubst l := PowerSeries.HasSubst.of_constantCoeff_zero' hl0
  have ha' : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [← PowerSeries.subst_comp_subst_apply hs ha', ex_l hex0 hinv, PowerSeries.subst_X ha']
end PI.PhNormUnits.UnitaryGroupMassFormula
