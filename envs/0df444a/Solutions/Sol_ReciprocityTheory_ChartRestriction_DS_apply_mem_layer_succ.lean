-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.apply_mem_layer_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:41:07.863737+00:00
-- url     : https://prove2.me/submissions/bc6bdd7f-36e2-4d17-ab39-8d66fafc3c4f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_layer_le_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_apply_mem_layer_succ_nc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_layer_kStable

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
variable {M : Type*} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hE : IsGlRep E) (hV : IsKStableSub ε E V) (a b : Fin n) {k : ℕ}
    {v : M} (hv : v ∈ layer ε E V k) : E a b v ∈ layer ε E V (k + 1) := by
  by_cases hab : ε a = ε b
  · exact layer_le_succ k (layer_kStable hE hV k a b hab v hv)
  · exact apply_mem_layer_succ_nc hab hv
end ReciprocityTheory.ChartRestriction.DS
