-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.wordContraction_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:51:33.368799+00:00
-- url     : https://prove2.me/submissions/ae3d5c19-a05a-4ea3-b374-b17f714607e2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PositionPrependMemNoncompactPositionSubmodule
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_coord_apply__ef209eafcd1f

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
theorem _root_.solution (k : ℕ) (F : Big n k M) :
    phi E k F = ∑ κ, word E κ (F κ) := by
  first
  | simp only [phi, LinearMap.coeFn_sum, Finset.sum_apply, LinearMap.comp_apply, coord_apply']
  | (rw [phi, LinearMap.sum_apply]; rfl)
  | simp [phi, coord_apply']
end ReciprocityTheory.ChartRestriction.DS
