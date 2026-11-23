-- Prove2me | solution 1 for PI.FglTriFactor.Wk.pr_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:56:08.420145+00:00
-- url     : https://prove2.me/submissions/7b32ce9d-4f01-4b90-b8b3-0cec9cacfff7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglTriFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_CoeffSubstUpdZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_PairSubstXZero
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
theorem _root_.solution {S : Subring ℂ_[p]} {x y : MvPowerSeries τ ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) (hxS : x ∈ SerS S τ) (hyS : y ∈ SerS S τ)
    {f : MvPowerSeries (Fin 2) ℂ_[p]} (hf : f ∈ SerS S (Fin 2)) : pr x y f ∈ SerS S τ := by
  show MvPowerSeries.subst ![x, y] f ∈ PI.AddIntG.Wk.SerS S τ
  exact PI.AddIntG.Wk.mvsubst_mem_SerS S (forall_fin_two_vec_of_both (fun z => MvPowerSeries.constantCoeff z = 0) hx hy)
    (forall_fin_two_vec_of_both (fun z => z ∈ PI.AddIntG.Wk.SerS S τ) hxS hyS) hf
end PI.FglTriFactor.Wk
