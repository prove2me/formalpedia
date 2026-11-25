-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.add_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:25:21.723499+00:00
-- url     : https://prove2.me/submissions/daff14ae-e2a3-4ca0-8d0b-9626371f2979

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
theorem _root_.solution (a : MvPowerSeries τ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0) :
    add l ex a a = mulBy l ex 2 a := by
  rw [show (2 : ℂ_[p]) = 1 + 1 by norm_num, ← add_mulBy hex0 hinv 1 1 a ha, mulBy_one hex0 hinv a ha]
end PI.PhNormUnits.UnitaryGroupMassFormula
