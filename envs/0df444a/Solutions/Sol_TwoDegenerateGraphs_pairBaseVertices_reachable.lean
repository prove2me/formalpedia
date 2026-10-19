-- Prove2me | solution 1 for TwoDegenerateGraphs.pairBaseVertices_reachable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/70700428-be3f-4bbe-b5f0-7177879ad442

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_ParentSystem_graph_adj_iff

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution (baseSize depth : ℕ)
    (hdepth : 0 < depth) (a b : Fin baseSize) :
    (pairParentSystem baseSize depth).graph.Reachable
      (pairBaseVertex baseSize depth a)
      (pairBaseVertex baseSize depth b) := by
  classical
  letI pairDecidableEq : DecidableEq (PairLayer baseSize 0) := Classical.decEq _
  by_cases hab : a = b
  · subst b
    exact SimpleGraph.Reachable.rfl
  · let pair : PairLayer baseSize 1 :=
      ⟨{a, b}, Finset.card_pair hab⟩
    let bridge := pairLayerEmbedding baseSize depth 1 (by omega) pair
    have hadj (x : Fin baseSize) (hx : x = a ∨ x = b) :
        (pairParentSystem baseSize depth).graph.Adj
          bridge (pairBaseVertex baseSize depth x) := by
      apply (ParentSystem.graph_adj_iff _ bridge _).mpr
      constructor
      · intro heq
        have hlevels := congrArg
          (fun z : PairVertex baseSize depth => z.1.val) heq
        change 1 = 0 at hlevels
        omega
      · left
        change pairBaseVertex baseSize depth x ∈
          pairParents baseSize depth bridge
        have hxmem : x ∈ ({a, b} : Finset (PairLayer baseSize 0)) := by
          rcases hx with hxa | hxb
          · rw [hxa]
            exact @Finset.mem_insert_self (PairLayer baseSize 0)
              pairDecidableEq a ({b} : Finset (PairLayer baseSize 0))
          · rw [hxb]
            exact @Finset.mem_insert_of_mem (PairLayer baseSize 0)
              pairDecidableEq ({b} : Finset (PairLayer baseSize 0)) b a
              (Finset.mem_singleton_self b)
        change
          pairLayerEmbedding baseSize depth 0 (by omega) x ∈
            ({a, b} : Finset (PairLayer baseSize 0)).map
              (pairLayerEmbedding baseSize depth 0 (by omega))
        exact Finset.mem_map.mpr ⟨x, hxmem, rfl⟩
    exact (hadj a (Or.inl rfl)).symm.reachable.trans
      (hadj b (Or.inr rfl)).reachable
end TwoDegenerateGraphs
