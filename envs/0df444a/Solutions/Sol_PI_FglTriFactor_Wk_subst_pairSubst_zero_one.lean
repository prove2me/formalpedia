-- Prove2me | solution 1 for PI.FglTriFactor.Wk.subst_pairSubst_zero_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:39:57.425268+00:00
-- url     : https://prove2.me/submissions/48937f90-8c62-46b0-a2e7-fb21f5316f29

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_PairSubstXZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_FormalGroupLawExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_LiftedThirdRootSubXZeroNeZero
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
theorem _root_.solution (g : MvPowerSeries (Fin 2) ℂ_[p]) :
    MvPowerSeries.subst ![MvPowerSeries.X 0, MvPowerSeries.X 1, (0 : MvPowerSeries (Fin 2) ℂ_[p])]
      (pr (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (MvPowerSeries.X 1) g) = g := by
  have h3 : MvPowerSeries.HasSubst
      (![MvPowerSeries.X 0, MvPowerSeries.X 1, 0] : Fin 3 → MvPowerSeries (Fin 2) ℂ_[p]) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by fin_cases s <;> simp)
  have h2 : MvPowerSeries.HasSubst
      (![MvPowerSeries.X 0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 3) ℂ_[p]) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by fin_cases s <;> simp)
  rw [pr, MvPowerSeries.subst_comp_subst_apply h2 h3]
  have e : (fun s => MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 1, 0] :
      Fin 3 → MvPowerSeries (Fin 2) ℂ_[p])
      ((![MvPowerSeries.X 0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 3) ℂ_[p]) s)) =
      MvPowerSeries.X := by
    funext s
    fin_cases s <;> simp [MvPowerSeries.subst_X h3]
  rw [e, MvPowerSeries.subst_self]
  rfl
end PI.FglTriFactor.Wk
