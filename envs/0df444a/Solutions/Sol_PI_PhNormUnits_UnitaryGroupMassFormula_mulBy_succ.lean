-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.mulBy_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:25:19.811675+00:00
-- url     : https://prove2.me/submissions/f4505f74-a611-4986-a317-91d700d8b2b9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_add_mulBy
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_mulBy_one

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
theorem _root_.solution (k : ℕ) (a : MvPowerSeries τ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0) :
    mulBy l ex ((k + 1 : ℕ) : ℂ_[p]) a = add l ex (mulBy l ex (k : ℂ_[p]) a) a := by
  rw [show ((k + 1 : ℕ) : ℂ_[p]) = (k : ℂ_[p]) + 1 by push_cast; ring, ← add_mulBy hex0 hinv _ _ a ha,
    mulBy_one hex0 hinv a ha]
end PI.PhNormUnits.UnitaryGroupMassFormula
