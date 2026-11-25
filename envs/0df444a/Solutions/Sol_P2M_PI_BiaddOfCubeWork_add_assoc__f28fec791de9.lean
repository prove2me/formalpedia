-- Prove2me | solution 1 for P2M_PI_BiaddOfCubeWork_add_assoc__f28fec791de9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:38:59.891794+00:00
-- url     : https://prove2.me/submissions/b56d63ef-94e7-4041-b9ff-65546c6dfb17

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BiaddOfCube
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditiveCubes_ConstantCoeffLogEqZero
import Theorems.Thm_PI_BiaddOfCubeWork_constantCoeff_log_eq_zero
import Theorems.Thm_PI_BiaddOfCubeWork_subst_subst_log
import Theorems.Thm_PI_BiaddOfCubeWork_constantCoeff_subst_zero

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
open PI PI.BiaddOfCubeWork
open PI.BiaddOfCube
variable {p : ℕ} [Fact p.Prime]
variable {σ : Type*}
namespace PI.BiaddOfCubeWork
theorem _root_.solution {l ex : PowerSeries ℂ_[p]}
    (hex : PowerSeries.constantCoeff ex = 0) (h : PowerSeries.subst ex l = PowerSeries.X)
    (a b c : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) (hc : MvPowerSeries.constantCoeff c = 0) :
    add l ex (add l ex a b) c = add l ex a (add l ex b c) := by
  have hl := constantCoeff_log_eq_zero hex h
  have hla := constantCoeff_subst_zero hl a ha
  have hlb := constantCoeff_subst_zero hl b hb
  have hlc := constantCoeff_subst_zero hl c hc
  show PowerSeries.subst (PowerSeries.subst (add l ex a b) l + PowerSeries.subst c l) ex =
    PowerSeries.subst (PowerSeries.subst a l + PowerSeries.subst (add l ex b c) l) ex
  rw [show add l ex a b = PowerSeries.subst (PowerSeries.subst a l + PowerSeries.subst b l) ex from rfl,
    subst_subst_log hex h _ (by rw [map_add, hla, hlb, add_zero]),
    show add l ex b c = PowerSeries.subst (PowerSeries.subst b l + PowerSeries.subst c l) ex from rfl,
    subst_subst_log hex h _ (by rw [map_add, hlb, hlc, add_zero]), add_assoc]
end PI.BiaddOfCubeWork
