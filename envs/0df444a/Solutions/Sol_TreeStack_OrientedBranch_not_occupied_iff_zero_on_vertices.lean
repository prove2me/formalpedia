-- Prove2me | solution 1 for TreeStack.OrientedBranch.not_occupied_iff_zero_on_vertices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:27:57.636211+00:00
-- url     : https://prove2.me/submissions/cfd768d4-da1a-4a35-83cb-30d545ebb1dd

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
variable [DecidableEq V]
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (B : OrientedBranch T) (C : Configuration V) :
    ¬ B.Occupied C ↔ ∀ v ∈ B.vertices, C v = 0 := by
  constructor
  · intro h v hv
    apply Nat.eq_zero_of_not_pos
    intro hpos
    exact h ⟨v, hv, hpos⟩
  · intro hz hOcc
    rcases hOcc with ⟨v, hv, hpos⟩
    rw [hz v hv] at hpos
    omega
end TreeStack.OrientedBranch
