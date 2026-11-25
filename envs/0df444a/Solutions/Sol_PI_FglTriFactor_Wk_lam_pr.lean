-- Prove2me | solution 1 for PI.FglTriFactor.Wk.lam_pr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:40:47.844874+00:00
-- url     : https://prove2.me/submissions/4cad35f1-bbc6-436a-96ce-212336053399

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_PairSubstXZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_FormalGroupLawExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_LiftedThirdRootSubXZeroNeZero
import Theorems.Thm_PI_AddIntG_Wk_lam_mul
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
theorem _root_.solution {τ : Type*} (wq : PowerSeries ℂ_[p]) {x y : MvPowerSeries τ ℂ_[p]}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    (y - x) * pr x y (lam wq) = PowerSeries.subst y (wser wq) - PowerSeries.subst x (wser wq) := by
  have hb : MvPowerSeries.HasSubst (![x, y] : Fin 2 → MvPowerSeries τ ℂ_[p]) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by fin_cases s <;> simp [hx, hy])
  have hcomp : ∀ i : Fin 2, MvPowerSeries.subst ![x, y] (PI.AddIntG.Wk.wv wq i) =
      PowerSeries.subst ((![x, y] : Fin 2 → MvPowerSeries τ ℂ_[p]) i) (wser wq) := by
    intro i
    have hXi : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) ℂ_[p]) :=
      PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
    rw [PI.AddIntG.Wk.wv, PowerSeries.subst, MvPowerSeries.subst_comp_subst_apply hXi.const hb]
    simp only [MvPowerSeries.subst_X hb]
    rfl
  have h := congrArg (MvPowerSeries.subst ![x, y]) (PI.AddIntG.Wk.lam_mul wq)
  rw [MvPowerSeries.subst_mul hb, MvPowerSeries.subst_sub hb, MvPowerSeries.subst_sub hb, hcomp 1, hcomp 0] at h
  simp only [MvPowerSeries.subst_X hb, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero] at h
  exact h
end PI.FglTriFactor.Wk
