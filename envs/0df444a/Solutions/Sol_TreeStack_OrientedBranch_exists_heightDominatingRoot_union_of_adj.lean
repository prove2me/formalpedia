-- Prove2me | solution 1 for TreeStack.OrientedBranch.exists_heightDominatingRoot_union_of_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:32:37.049114+00:00
-- url     : https://prove2.me/submissions/17ebd5a1-90c2-4535-8806-5118583b5eed

import Mathlib
import Definitions.Def_TreeStack_HeightSource
import Definitions.Def_TreeStack_Consolidation
import Theorems.Thm_TreeStack_OrientedBranch_dist_eq_dist_add_one_add_dist_of_adj_disjoint_carriers

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (h : V → ℕ)
    {A B : Finset V}
    (hAConn : TreePathConnected (T := T) A)
    (hBConn : TreePathConnected (T := T) B)
    (hDisj : Disjoint A B)
    {a b r s : V}
    (ha : a ∈ A) (hb : b ∈ B)
    (hadj : T.graph.Adj a b)
    (hADom : HeightDominated (T := T) h A r)
    (hBDom : HeightDominated (T := T) h B s) :
    ∃ t : V,
      HeightDominated (T := T) h (A ∪ B) t := by
  rcases hADom with ⟨hrA, hAHeight⟩
  rcases hBDom with ⟨hsB, hBHeight⟩
  by_cases hDepth :
      T.graph.dist s b ≤ T.graph.dist r a + 1
  · refine ⟨r, Finset.mem_union_left _ hrA, ?_⟩
    intro v hv
    rw [Finset.mem_union] at hv
    rcases hv with hvA | hvB
    · exact hAHeight v hvA
    · have hCross :=
        dist_eq_dist_add_one_add_dist_of_adj_disjoint_carriers
          hAConn hBConn hDisj ha hb hadj hrA hvB
      have hTri :
          T.graph.dist s v ≤
            T.graph.dist s b + T.graph.dist b v :=
        T.isTree.connected.dist_triangle
      have hBase := hBHeight v hvB
      rw [hCross]
      omega
  · have hDepth' :
        T.graph.dist r a ≤ T.graph.dist s b + 1 := by
      omega
    refine ⟨s, Finset.mem_union_right _ hsB, ?_⟩
    intro v hv
    rw [Finset.mem_union] at hv
    rcases hv with hvA | hvB
    · have hCross :=
        dist_eq_dist_add_one_add_dist_of_adj_disjoint_carriers
          hBConn hAConn hDisj.symm hb ha hadj.symm hsB hvA
      have hTri :
          T.graph.dist r v ≤
            T.graph.dist r a + T.graph.dist a v :=
        T.isTree.connected.dist_triangle
      have hBase := hAHeight v hvA
      rw [hCross]
      omega
    · exact hBHeight v hvB
end TreeStack.OrientedBranch
