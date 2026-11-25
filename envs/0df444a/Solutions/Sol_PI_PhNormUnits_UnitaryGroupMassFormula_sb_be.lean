-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.sb_be
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:57:45.112922+00:00
-- url     : https://prove2.me/submissions/ec64078a-50f7-4fcc-9189-d286fcc93049

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_constantCoeff_formalAdd
import Theorems.Thm_P2M_PI_PhNormUnits_UnitaryGroupMassFormula_sb_sub__5014b8493f84
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_sb_add
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_sb_phAt

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
variable (hex0 : PowerSeries.constantCoeff ex = 0) (hinv : PowerSeries.subst ex l = PowerSeries.X)
include hex0 hinv
namespace PI.PhNormUnits.UnitaryGroupMassFormula
theorem _root_.solution (ph : PowerSeries ℂ_[p]) (a b : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) :
    MvPowerSeries.subst s (be l ex ph a b) =
      be l ex ph (MvPowerSeries.subst s a) (MvPowerSeries.subst s b) := by
  unfold be
  rw [sb_sub' s hs, sb_sub' s hs, sb_phAt s hs ph _ (constantCoeff_formalAdd hex0 hinv a b ha hb), sb_add s hs hex0 hinv a b ha hb,
    sb_phAt s hs ph a ha, sb_phAt s hs ph b hb]
end PI.PhNormUnits.UnitaryGroupMassFormula
