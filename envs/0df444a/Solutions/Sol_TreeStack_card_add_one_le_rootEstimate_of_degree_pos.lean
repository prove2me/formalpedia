-- Prove2me | solution 1 for TreeStack.card_add_one_le_rootEstimate_of_degree_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:11:48.306989+00:00
-- url     : https://prove2.me/submissions/a1d76c29-da36-4fdb-a8ab-8ec241d1f369

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Estimator
import Theorems.Thm_TreeStack_rootEstimate_corrected_expansion
import Theorems.Thm_TreeStack_card_erase_root_eq_leafCount_add_internal
import Theorems.Thm_TreeStack_card_internal_le_weighted_sum
import Theorems.Thm_TreeStack_mem_support_iff
attribute [local simp] TreeStack.mem_support_iff



set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
namespace TreeStack
theorem _root_.solution
    {V : Type*} [Fintype V] (T : FiniteTree V) (r : V)
    (hdeg : ∀ v, 0 < T.graph.degree v) :
    Fintype.card V + 1 ≤ rootEstimate T r := by
  have hpart := card_erase_root_eq_leafCount_add_internal T r hdeg
  have herase :=
    Finset.card_erase_add_one (s := (Finset.univ : Finset V))
      (a := r) (Finset.mem_univ r)
  have hsum := card_internal_le_weighted_sum T r
  have hroot := hdeg r
  simp only [Finset.card_univ] at herase
  rw [rootEstimate_corrected_expansion]
  omega
end TreeStack
