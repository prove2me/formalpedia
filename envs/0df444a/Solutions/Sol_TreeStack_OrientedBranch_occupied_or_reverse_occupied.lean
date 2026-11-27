-- Prove2me | solution 1 for TreeStack.OrientedBranch.occupied_or_reverse_occupied
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:00:02.112808+00:00
-- url     : https://prove2.me/submissions/56b82f0b-30df-49b5-a3e4-c42543846201

import Mathlib
import Definitions.Def_TreeStack_Defect
import Definitions.Def_TreeStack_Support
import Theorems.Thm_TreeStack_OrientedBranch_mem_vertices_or_mem_reverseBranch

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (C : Configuration V) (B : OrientedBranch T)
    {x : V} (hx : 0 < C x) :
    B.Occupied C ∨ B.reverseBranch.Occupied C := by
  rcases B.mem_vertices_or_mem_reverseBranch x with hxB | hxR
  · exact Or.inl ⟨x, hxB, hx⟩
  · exact Or.inr ⟨x, hxR, hx⟩
end TreeStack.OrientedBranch
