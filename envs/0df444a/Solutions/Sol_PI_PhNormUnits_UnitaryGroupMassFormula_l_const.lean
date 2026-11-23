-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.l_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:32.309577+00:00
-- url     : https://prove2.me/submissions/200cff13-b745-4a04-a94f-6847de860e9b

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
variable {l ex : PowerSeries ℂ_[p]}
namespace PI.PhNormUnits.UnitaryGroupMassFormula
theorem _root_.solution (hex0 : PowerSeries.constantCoeff ex = 0)
    (hinv : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.constantCoeff l = 0 := by
  have h1 := congrArg (MvPowerSeries.constantCoeff (σ := Unit) (R := ℂ_[p])) hinv
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hex0)] at h1
  rw [finsum_eq_single _ 0] at h1
  · have h2 : PowerSeries.constantCoeff l =
        MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries ℂ_[p]) := by
      simpa using h1
    exact h2.trans PowerSeries.constantCoeff_X
  · intro d hd
    rw [map_pow]
    change PowerSeries.coeff d l • (PowerSeries.constantCoeff ex) ^ d = 0
    rw [hex0, zero_pow hd, smul_zero]
end PI.PhNormUnits.UnitaryGroupMassFormula
