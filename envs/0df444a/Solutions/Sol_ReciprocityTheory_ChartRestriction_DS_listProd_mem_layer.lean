-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.listProd_mem_layer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:22:40.632862+00:00
-- url     : https://prove2.me/submissions/ffbbf642-9594-4c96-9225-6e1f698b2456

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PositionPrependMemNoncompactPositionSubmodule
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PhiPerm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_apply_mem_layer_succ


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
theorem _root_.solution (hE : IsGlRep E) (hV : IsKStableSub ε E V)
    (l : List (Fin n × Fin n)) {j : ℕ} {v : M} (hv : v ∈ layer ε E V j) :
    (l.map fun p => E p.1 p.2).prod v ∈ layer ε E V (j + l.length) := by
  induction l with
  | nil => simpa using hv
  | cons p l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, List.length_cons, ← add_assoc]
    exact apply_mem_layer_succ hE hV p.1 p.2 ih
end ReciprocityTheory.ChartRestriction.DS
