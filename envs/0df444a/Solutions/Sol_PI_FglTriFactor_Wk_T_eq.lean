-- Prove2me | solution 1 for PI.FglTriFactor.Wk.T_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:54:29.749253+00:00
-- url     : https://prove2.me/submissions/c24d2c44-f0cb-4381-bec4-7827797a0f99

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_PairSubstXZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_FormalGroupLawExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_LiftedThirdRootSubXZeroNeZero
import Theorems.Thm_PI_FglTriFactor_Wk_wser_X
import Theorems.Thm_PI_FglTriFactor_Wk_lam_pr
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_mvsubst_mem_SerS


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FglTriFactor PI.FglTriFactor.Wk
open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS lam nu wser wv Z3)
variable {p : ℕ} [Fact p.Prime]
namespace PI.FglTriFactor.Wk
theorem _root_.solution (wq : PowerSeries ℂ_[p]) :
    T wq = (MvPowerSeries.X 1 - MvPowerSeries.X 0) * (MvPowerSeries.X 2 - MvPowerSeries.X 0) * (Lac wq - Lab wq) := by
  have hAB := lam_pr wq (x := (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p])) (y := MvPowerSeries.X 1)
    (MvPowerSeries.constantCoeff_X _) (MvPowerSeries.constantCoeff_X _)
  have hAC := lam_pr wq (x := (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p])) (y := MvPowerSeries.X 2)
    (MvPowerSeries.constantCoeff_X _) (MvPowerSeries.constantCoeff_X _)
  rw [wser_X, wser_X] at hAB hAC
  simp only [T, Lab, Lac]
  linear_combination (MvPowerSeries.X 2 - MvPowerSeries.X 0) * hAB - (MvPowerSeries.X 1 - MvPowerSeries.X 0) * hAC
end PI.FglTriFactor.Wk
