-- Prove2me | solution 1 for TreeStack.card_add_one_le_rootEstimate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:13:29.772413+00:00
-- url     : https://prove2.me/submissions/2934bba5-dccf-4d8a-962c-f63101e57866

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Estimator
import Theorems.Thm_TreeStack_card_add_one_le_rootEstimate_of_degree_pos

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
namespace TreeStack
theorem _root_.solution {V : Type*} [Fintype V] [Nontrivial V]
    (T : FiniteTree V) (r : V) :
    Fintype.card V + 1 ≤ rootEstimate T r := by
  apply card_add_one_le_rootEstimate_of_degree_pos T r
  intro v
  exact T.isTree.connected.preconnected.degree_pos_of_nontrivial v
end TreeStack
