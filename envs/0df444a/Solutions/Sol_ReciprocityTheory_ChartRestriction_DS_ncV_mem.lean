-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.ncV_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:53:38.642866+00:00
-- url     : https://prove2.me/submissions/7f352333-b935-4b9c-ba0f-bd7e485320bb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigRep
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_mem_ncV_iff

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
theorem _root_.solution {k : ℕ} {F : Big n k M} (hF : F ∈ ncV ε V k) (κ : Fin k → Fin n × Fin n) :
    F κ ∈ V := by
  have h := (mem_ncV_iff F).1 hF κ
  split_ifs at h
  · exact h
  · rw [(Submodule.mem_bot ℂ).1 h]
    exact V.zero_mem
end ReciprocityTheory.ChartRestriction.DS
