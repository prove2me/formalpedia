-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.casimirK_mem_of_kStable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:10:00.884951+00:00
-- url     : https://prove2.me/submissions/8f5721f1-2e09-4189-965d-0af3bd694f60

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KUnitB

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
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {S : Submodule ℂ X} (hS : IsKStableSub ε A S) {x : X} (hx : x ∈ S) : casimirK ε A x ∈ S := by
  unfold casimirK
  simp only [LinearMap.sum_apply, Module.End.mul_apply]
  refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b hb => ?_
  have hab : ε b = ε a := (Finset.mem_filter.mp hb).2
  exact hS a b hab.symm _ (hS b a hab _ hx)
end ReciprocityTheory.ChartRestriction.DS
