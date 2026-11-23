-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.sb_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:39.629806+00:00
-- url     : https://prove2.me/submissions/a40d6b52-24bf-4bd9-b4ea-8361d483eeb5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_constantCoeff_subst_log
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_sb_psubst
import Theorems.Thm_P2M_PI_PhNormUnits_UnitaryGroupMassFormula_sb_add__b34afe4daad2

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
theorem _root_.solution (a b : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) :
    MvPowerSeries.subst s (add l ex a b) = add l ex (MvPowerSeries.subst s a) (MvPowerSeries.subst s b) := by
  unfold add
  rw [sb_psubst s hs _ (by rw [map_add, constantCoeff_subst_log hex0 hinv a ha, constantCoeff_subst_log hex0 hinv b hb, add_zero]),
    sb_add' s hs, sb_psubst s hs a ha, sb_psubst s hs b hb]
end PI.PhNormUnits.UnitaryGroupMassFormula
