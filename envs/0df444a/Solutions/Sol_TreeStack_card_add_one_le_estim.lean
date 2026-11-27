-- Prove2me | solution 1 for TreeStack.card_add_one_le_estim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:15:02.794691+00:00
-- url     : https://prove2.me/submissions/a809d927-a14d-479b-b836-960ef1f66cbb

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Estimator
import Theorems.Thm_TreeStack_card_add_one_le_rootEstimate
import Theorems.Thm_TreeStack_rootEstimate_le_estim

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
namespace TreeStack
theorem _root_.solution {V : Type*} [Fintype V] [Nontrivial V]
    (T : FiniteTree V) :
    Fintype.card V + 1 ≤ estim T := by
  let r : V := T.isTree.connected.nonempty.some
  exact (card_add_one_le_rootEstimate T r).trans (rootEstimate_le_estim T r)
end TreeStack
