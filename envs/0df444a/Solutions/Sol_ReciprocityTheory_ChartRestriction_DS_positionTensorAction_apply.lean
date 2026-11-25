-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.positionTensorAction_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:25:07.826977+00:00
-- url     : https://prove2.me/submissions/5ee112bc-2e84-48f3-9360-ddbfb24a01cd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PositionPrependMemNoncompactPositionSubmodule
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_coord_apply__ef209eafcd1f
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_mAct_apply__d8d50007d2d3

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
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (k : ℕ) (a b : Fin n) (F : Big n k M) (κ : Fin k → Fin n × Fin n) :
    bAct E k a b F κ = E a b (F κ) + ∑ i, factorAd (M := M) k i a b F κ := by
  rw [← coord_apply' k κ (bAct E k a b F)]
  first
  | (simp only [bAct, LinearMap.add_apply, LinearMap.coeFn_sum, Finset.sum_apply, map_add, map_sum]
     simp only [coord_apply', mAct_apply'])
  | (simp only [bAct, LinearMap.add_apply, LinearMap.sum_apply, map_add, map_sum]
     simp only [coord_apply', mAct_apply'])
end ReciprocityTheory.ChartRestriction.DS
