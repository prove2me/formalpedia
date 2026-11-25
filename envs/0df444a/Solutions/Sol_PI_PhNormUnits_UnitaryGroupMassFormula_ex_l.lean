-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.ex_l
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:10:16.371797+00:00
-- url     : https://prove2.me/submissions/0d7a30a3-40b4-42b3-b22d-4d41b5a838e1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_l_const
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_coeff_one_l_ne

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
variable {l ex : PowerSeries ℂ_[p]}
namespace PI.PhNormUnits.UnitaryGroupMassFormula
theorem _root_.solution (hex0 : PowerSeries.constantCoeff ex = 0)
    (hinv : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.subst l ex = PowerSeries.X := by
  have hl0 := l_const hex0 hinv
  have hu : IsUnit (PowerSeries.coeff 1 l) := isUnit_iff_ne_zero.mpr (coeff_one_l_ne hex0 hinv)
  set Q := PowerSeries.substInvOfIsUnit l hu
  have hQl : PowerSeries.subst l Q = PowerSeries.X := PowerSeries.subst_substInvOfIsUnit_left l hl0 hu
  have hexQ : ex = Q := by
    have hs : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex0
    have hsl : PowerSeries.HasSubst l := PowerSeries.HasSubst.of_constantCoeff_zero' hl0
    calc ex = PowerSeries.subst ex (PowerSeries.X : PowerSeries ℂ_[p]) := (PowerSeries.subst_X hs).symm
      _ = PowerSeries.subst ex (PowerSeries.subst l Q) := by rw [hQl]
      _ = PowerSeries.subst (PowerSeries.subst ex l) Q := PowerSeries.subst_comp_subst_apply hsl hs Q
      _ = PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[p]) Q := by rw [hinv]
      _ = Q := PowerSeries.X_subst Q
  rw [hexQ]; exact hQl
end PI.PhNormUnits.UnitaryGroupMassFormula
