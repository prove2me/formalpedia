-- Prove2me | solution 1 for PI.FglTriFactor.Wk.pr_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:56:28.423032+00:00
-- url     : https://prove2.me/submissions/b5fd7b17-e583-466d-bc33-ec98fa69d369

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglTriFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_CoeffSubstUpdZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_PairSubstXZero
import Theorems.Thm_PI_FglTriFactor_Wk_hasSubst_pr
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
open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS)
variable {p : ℕ} [Fact p.Prime]
variable {τ : Type*}
namespace PI.FglTriFactor.Wk
theorem _root_.solution {υ : Type*} {b : τ → MvPowerSeries υ ℂ_[p]} (hb : MvPowerSeries.HasSubst b)
    {x y : MvPowerSeries τ ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) (f : MvPowerSeries (Fin 2) ℂ_[p]) :
    MvPowerSeries.subst b (pr x y f) = pr (MvPowerSeries.subst b x) (MvPowerSeries.subst b y) f := by
  unfold pr
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_pr hx hy) hb]
  congr 1
  funext i
  fin_cases i <;> rfl
end PI.FglTriFactor.Wk
