-- Prove2me | solution 1 for PI.FglTriFactor.Wk.cc_pr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:39:36.575715+00:00
-- url     : https://prove2.me/submissions/e44e0435-4fc8-436a-81e2-acd516e2de36

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
section
noncomputable section
namespace PI.FglTriFactor.Wk
open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS)
variable {p : ℕ} [Fact p.Prime]
section Ops
variable {l ex : PowerSeries ℂ_[p]} {σ τ : Type*}
end Ops
section Pair
variable {τ : Type*}
private theorem forall_fin_two_vec_of_both {α : Type*} (P : α → Prop) {x y : α} (hx : P x) (hy : P y) :
    ∀ i : Fin 2, P (![x, y] i) := by
  intro i
  fin_cases i
  exacts [hx, hy]
end Pair
end PI.FglTriFactor.Wk
end
end

set_option autoImplicit false
noncomputable section
open PI PI.FglTriFactor PI.FglTriFactor.Wk
open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS)
variable {p : ℕ} [Fact p.Prime]
variable {τ : Type*}
namespace PI.FglTriFactor.Wk
theorem _root_.solution {x y : MvPowerSeries τ ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) {f : MvPowerSeries (Fin 2) ℂ_[p]}
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (pr x y f) = 0 := by
  show MvPowerSeries.constantCoeff (MvPowerSeries.subst ![x, y] f) = 0
  exact MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_pr hx hy)
    (forall_fin_two_vec_of_both (fun z => MvPowerSeries.constantCoeff z = 0) hx hy) hf
end PI.FglTriFactor.Wk
