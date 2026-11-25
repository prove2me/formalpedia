-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_wordContraction_mem_noncompactLayer__4b3537922a04
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:33:46.065697+00:00
-- url     : https://prove2.me/submissions/ec1cf20d-007e-4a90-bade-dbd182bc5cd2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PositionPrependMemNoncompactPositionSubmodule
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_wordContraction_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rootWordProduct_mem_noncompactLayer
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_mem_noncompactPositionSubmodule_iff__607b2d11fea7

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
theorem _root_.solution {k : ℕ} {F : Big n k M} (hF : F ∈ ncV ε V k) :
    phi E k F ∈ layer ε E V k := by
  rw [wordContraction_apply]
  refine Submodule.sum_mem _ fun κ _ => ?_
  have h := mem_noncompactPositionSubmodule_iff'.mp hF κ
  split_ifs at h with hκ
  · exact rootWordProduct_mem_noncompactLayer κ hκ _ h
  · rw [Submodule.mem_bot] at h
    rw [h, map_zero]
    exact Submodule.zero_mem _
end ReciprocityTheory.ChartRestriction.DS
