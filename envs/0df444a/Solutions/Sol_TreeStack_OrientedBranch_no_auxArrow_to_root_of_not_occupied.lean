-- Prove2me | solution 1 for TreeStack.OrientedBranch.no_auxArrow_to_root_of_not_occupied
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:11:20.396106+00:00
-- url     : https://prove2.me/submissions/0eea6c86-552e-46af-97f3-b1346d6c8028

import Mathlib
import Definitions.Def_TreeStack_DefectCharge
import Definitions.Def_TreeStack_Auxiliary
import Theorems.Thm_TreeStack_OrientedBranch_auxArrow_supportEdge
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_vertices_subset


set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (C : Configuration V) (ambientRoot : V)
    (B : OrientedBranch T) (hEmpty : ¬ B.Occupied C) (u : V) :
    ¬ AuxArrow (T := T) C ambientRoot u B.root := by
  intro hArrow
  have hAdj := auxArrow_adj C ambientRoot hArrow
  have hSupport := auxArrow_supportEdge C ambientRoot hArrow
  by_cases hup : u = B.parent
  · subst u
    have hBranch :
        incidentBranch T B.root B.parent hAdj = B.reverseBranch := by
      cases B
      rfl
    rw [hBranch] at hSupport
    exact hEmpty hSupport.2
  · let c : B.Child :=
      { vertex := u
        adj := hAdj.symm
        ne_parent := hup }
    have hBranch :
        incidentBranch T B.root u hAdj = B.childBranch c := by
      rfl
    rw [hBranch] at hSupport
    rcases hSupport.1 with ⟨x, hx, hxPos⟩
    exact hEmpty ⟨x, B.childBranch_vertices_subset c hx, hxPos⟩
end TreeStack.OrientedBranch
