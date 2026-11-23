-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_mem_noncompactPositionSubmodule_iff__607b2d11fea7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:51:45.336689+00:00
-- url     : https://prove2.me/submissions/e6a0b22a-7beb-4f9e-9859-4dfdea63fca1

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
theorem _root_.solution {k : ℕ} {F : Big n k M} :
    F ∈ ncV ε V k ↔ ∀ κ, F κ ∈ (if ∀ i, ε (κ i).1 ≠ ε (κ i).2 then V else ⊥) := by
  first
  | (rw [ncV, Submodule.mem_iInf]; rfl)
  | simp only [ncV, Submodule.mem_iInf, Submodule.mem_comap, coord_apply']
end ReciprocityTheory.ChartRestriction.DS
