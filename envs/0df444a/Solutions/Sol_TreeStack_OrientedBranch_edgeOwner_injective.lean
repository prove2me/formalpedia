-- Prove2me | solution 1 for TreeStack.OrientedBranch.edgeOwner_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:26:07.17383+00:00
-- url     : https://prove2.me/submissions/9d0e25a5-5a24-4d8a-a0af-215a7317a47f

import Mathlib
import Definitions.Def_TreeStack_AuxiliaryCharge
import Definitions.Def_TreeStack_GlobalCharge
import Theorems.Thm_TreeStack_OrientedBranch_edgeBranch_edge
import Theorems.Thm_TreeStack_OrientedBranch_edge_eq_of_rootedOwner_eq


set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution (ambientRoot : V) :
    Function.Injective (edgeOwner (T := T) ambientRoot) := by
  intro e f hOwner
  apply Subtype.ext
  have hEdge :=
    edge_eq_of_rootedOwner_eq ambientRoot
      (edgeBranch (T := T) e) (edgeBranch (T := T) f) hOwner
  rw [edgeBranch_edge (T := T) e, edgeBranch_edge (T := T) f] at hEdge
  exact hEdge
end TreeStack.OrientedBranch
