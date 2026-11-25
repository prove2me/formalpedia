-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.casimir_mem_genSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:23:36.692675+00:00
-- url     : https://prove2.me/submissions/e18df818-374c-4133-a7c2-739f68c2eb53

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_SchForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCore
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_prFst_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_prSnd_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.prFst_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.prSnd_apply



set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    {V : Submodule ℂ M} {w : M} (hw : w ∈ V) : casimir E w ∈ genSub E V := by
  rw [genSub, Submodule.mem_sInf]
  rintro T ⟨hVT, hT⟩
  show (∑ a, ∑ b, E a b * E b a) w ∈ T
  first
    | (rw [LinearMap.sum_apply]
       refine Submodule.sum_mem _ fun a _ => ?_
       rw [LinearMap.sum_apply]
       exact Submodule.sum_mem _ fun b _ => hT a b _ (hT b a _ (hVT hw)))
    | (simp only [LinearMap.coeFn_sum, Finset.sum_apply]
       exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => hT a b _ (hT b a _ (hVT hw)))
end ReciprocityTheory.ChartRestriction.DS
