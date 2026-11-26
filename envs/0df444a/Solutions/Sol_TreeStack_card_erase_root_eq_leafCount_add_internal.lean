-- Prove2me | solution 1 for TreeStack.card_erase_root_eq_leafCount_add_internal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:07:48.838781+00:00
-- url     : https://prove2.me/submissions/964420ce-3451-4da0-9aa7-0342e3d915a9

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Estimator
import Theorems.Thm_TreeStack_erase_root_eq_leaf_union_internal
import Theorems.Thm_TreeStack_leafVertices_disjoint_internal

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
namespace TreeStack
theorem _root_.solution {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V)
    (hdeg : ∀ v, 0 < T.graph.degree v) :
    ((Finset.univ : Finset V).erase r).card =
      leafCount T r + (nonRootInternalVertices T r).card := by
  rw [erase_root_eq_leaf_union_internal T r hdeg,
    Finset.card_union_of_disjoint (leafVertices_disjoint_internal T r)]
  rfl
end TreeStack
