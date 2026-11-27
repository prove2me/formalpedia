-- Prove2me | solution 1 for TreeStack.sum_rootBranch_vertices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:58:54.337483+00:00
-- url     : https://prove2.me/submissions/082c09fc-2d18-44f8-a23c-20994cbcc5d9

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack
theorem _root_.solution
    (T : FiniteTree V) (r : V) (f : V → ℕ) :
    (∑ n : RootNeighbor T r, ∑ x ∈ n.branch.vertices, f x) =
      ∑ x ∈ (Finset.univ : Finset V).erase r, f x := by
  classical
  calc
    (∑ n : RootNeighbor T r, ∑ x ∈ n.branch.vertices, f x) =
        ∑ n : RootNeighbor T r,
          ∑ x : {x : V // x ∈ n.branch.vertices}, f x.1 := by
            apply Finset.sum_congr rfl
            intro n _
            rw [Finset.sum_subtype
              n.branch.vertices
              (fun _ => Iff.rfl) f]
    _ = ∑ z : RootBranchVertex T r, f z.2.1 := by
          rw [Fintype.sum_sigma]
    _ = ∑ x : RootProperVertex r, f x.1 := by
          exact
            Fintype.sum_equiv
              (rootBranchVertexEquivProper T r)
              (fun z : RootBranchVertex T r => f z.2.1)
              (fun x : RootProperVertex r => f x.1)
              (fun _ => rfl)
    _ = ∑ x ∈ (Finset.univ : Finset V).erase r, f x := by
          symm
          exact
            Finset.sum_subtype
              ((Finset.univ : Finset V).erase r)
              (fun _ => Iff.rfl) f
end TreeStack
