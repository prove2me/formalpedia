-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.be_add_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:38:58.668817+00:00
-- url     : https://prove2.me/submissions/bb225e19-1592-454b-a8a8-1ec87229db91

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_TendstoCoeffOfCont
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffVar
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_be_add_left
import Theorems.Thm_P2M_PI_PhNormUnits_UnitaryGroupMassFormula_add_comm__cbec21b12115


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
variable {ph : PowerSeries ℂ_[p]}
  (hB : Simeq (be l ex ph (add l ex (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (be l ex ph (Xv 0) (Xv 2) + be l ex ph (Xv 1) (Xv 2)))
include hSub hex0 hinv hB
namespace PI.PhNormUnits.UnitaryGroupMassFormula
theorem _root_.solution {τ : Type} (x y z : MvPowerSeries τ ℂ_[p]) (hx0 : MvPowerSeries.constantCoeff x = 0)
    (hy0 : MvPowerSeries.constantCoeff y = 0) (hz0 : MvPowerSeries.constantCoeff z = 0)
    (hx : IntegralMv x) (hy : IntegralMv y) (hz : IntegralMv z) :
    Simeq (be l ex ph z (add l ex x y)) (be l ex ph z x + be l ex ph z y) := by

  have hsym : ∀ a b : MvPowerSeries τ ℂ_[p], be l ex ph a b = be l ex ph b a := by
    intro a b
    unfold be
    rw [add_comm']
    ring
  rw [hsym z (add l ex x y), hsym z x, hsym z y]
  exact be_add_left hSub hex0 hinv hB x y z hx0 hy0 hz0 hx hy hz
end PI.PhNormUnits.UnitaryGroupMassFormula
