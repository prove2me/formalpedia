-- Prove2me | solution 1 for TreeStack.OrientedBranch.sum_childBranch_vertices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:58:05.598267+00:00
-- url     : https://prove2.me/submissions/b23b046e-4e94-4040-aff6-b136c6267f2c

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
open TreeStack.OrientedBranch
namespace TreeStack.OrientedBranch
theorem _root_.solution (B : OrientedBranch T) (f : V → ℕ) :
    (∑ c : B.Child, ∑ x ∈ (B.childBranch c).vertices, f x) =
      ∑ x ∈ B.vertices.erase B.root, f x := by
  classical
  calc
    (∑ c : B.Child, ∑ x ∈ (B.childBranch c).vertices, f x) =
        ∑ c : B.Child,
          ∑ x : {x : V // x ∈ (B.childBranch c).vertices}, f x.1 := by
            apply Finset.sum_congr rfl
            intro c _
            rw [Finset.sum_subtype
              (B.childBranch c).vertices
              (fun _ => Iff.rfl) f]
    _ = ∑ z : B.ChildVertex, f z.2.1 := by
          rw [Fintype.sum_sigma]
    _ = ∑ x : B.ProperVertex, f x.1 := by
          exact
            Fintype.sum_equiv B.childVertexEquivProper
              (fun z : B.ChildVertex => f z.2.1)
              (fun x : B.ProperVertex => f x.1)
              (fun _ => rfl)
    _ = ∑ x ∈ B.vertices.erase B.root, f x := by
          symm
          exact
            Finset.sum_subtype
              (B.vertices.erase B.root)
              (fun _ => Iff.rfl) f
end TreeStack.OrientedBranch
