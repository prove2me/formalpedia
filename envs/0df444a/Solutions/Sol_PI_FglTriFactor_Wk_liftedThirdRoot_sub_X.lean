-- Prove2me | solution 1 for PI.FglTriFactor.Wk.liftedThirdRoot_sub_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:49.93852+00:00
-- url     : https://prove2.me/submissions/58e31d05-adbe-41ec-a41e-db04c9747c4c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_PairSubstXZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_FormalGroupLawExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_LiftedThirdRootSubXZeroNeZero
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_mvsubst_mem_SerS
import Theorems.Thm_PI_FglTriFactor_Wk_subst_sub


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
theorem _root_.solution (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) (i : Fin 2) :
    s3 W wq - MvPowerSeries.X (Fin.castSucc i) = pr (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p])
      (MvPowerSeries.X 1) (Z3 W wq - MvPowerSeries.X i) := by
  have h2 : MvPowerSeries.HasSubst
      (![MvPowerSeries.X 0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 3) ℂ_[p]) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by fin_cases s <;> simp)
  simp only [s3, pr]
  rw [MvPowerSeries.subst_sub h2, MvPowerSeries.subst_X h2]
  fin_cases i <;> rfl
end PI.FglTriFactor.Wk
