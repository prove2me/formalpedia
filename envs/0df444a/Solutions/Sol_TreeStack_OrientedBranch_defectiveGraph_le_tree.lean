-- Prove2me | solution 1 for TreeStack.OrientedBranch.defectiveGraph_le_tree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:02:55.641908+00:00
-- url     : https://prove2.me/submissions/0af8c89c-1d71-47b4-8802-313ee80d8c16

import Mathlib
import Definitions.Def_TreeStack_Support
import Definitions.Def_TreeStack_ForestOwner

set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (C : Configuration V) :
    defectiveGraph (T := T) C ≤ T.graph := by
  intro u v huv
  rcases huv with ⟨h, _⟩
  exact h
end TreeStack.OrientedBranch
