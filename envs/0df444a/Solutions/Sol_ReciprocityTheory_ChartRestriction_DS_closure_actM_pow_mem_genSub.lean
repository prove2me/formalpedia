-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.closure_actM_pow_mem_genSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:29:59.857906+00:00
-- url     : https://prove2.me/submissions/ff9ab7fa-06e7-4ad8-9891-b78c7e792556

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Analytic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ClosureK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ExistsExpEqOfMemKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Closure
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_closure_E_mem_genSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {V : Submodule ℂ D} (X : Matrix (Fin n) (Fin n) ℂ) (m : ℕ)
    {v : D} (hv : v ∈ genSub E V) : ((actM E X) ^ m) v ∈ genSub E V := by
  induction m with
  | zero => simpa using hv
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, actM, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun b _ => ?_
    rw [LinearMap.smul_apply]
    exact Submodule.smul_mem _ _ (closure_E_mem_genSub a b ih)
end ReciprocityTheory.ChartRestriction.DS
