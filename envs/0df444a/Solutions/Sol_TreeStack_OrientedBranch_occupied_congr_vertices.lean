-- Prove2me | solution 1 for TreeStack.OrientedBranch.occupied_congr_vertices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:28:56.562023+00:00
-- url     : https://prove2.me/submissions/4aa68f5d-8058-46ed-aaa3-bbb5b950b59f

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (B : OrientedBranch T) (C D : Configuration V)
    (hCD : ∀ v ∈ B.vertices, C v = D v) :
    B.Occupied C ↔ B.Occupied D := by
  constructor
  · rintro ⟨v, hv, hpos⟩
    refine ⟨v, hv, ?_⟩
    rw [← hCD v hv]
    exact hpos
  · rintro ⟨v, hv, hpos⟩
    refine ⟨v, hv, ?_⟩
    rw [hCD v hv]
    exact hpos
end TreeStack.OrientedBranch
