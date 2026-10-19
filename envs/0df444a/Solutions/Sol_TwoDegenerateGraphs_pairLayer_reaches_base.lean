-- Prove2me | solution 1 for TwoDegenerateGraphs.pairLayer_reaches_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/410e2131-8e92-41e6-8458-9876dd9ee5f0

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_ParentSystem_graph_adj_iff

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution (baseSize depth : ℕ) :
    ∀ (i : ℕ) (hi : i < depth + 1) (v : PairLayer baseSize i),
      ∃ a : Fin baseSize,
        (pairParentSystem baseSize depth).graph.Reachable
          (pairLayerEmbedding baseSize depth i hi v)
          (pairBaseVertex baseSize depth a) := by
  intro i
  induction i with
  | zero =>
      intro hi v
      exact ⟨v, SimpleGraph.Reachable.rfl⟩
  | succ i ih =>
      intro hi v
      change {parents : Finset (PairLayer baseSize i) // parents.card = 2} at v
      have hnonempty : v.val.Nonempty := by
        apply Finset.card_pos.mp
        omega
      obtain ⟨parent, hparent⟩ := hnonempty
      let lower := pairLayerEmbedding baseSize depth i (by omega) parent
      let upper := pairLayerEmbedding baseSize depth (i + 1) hi v
      have hedge :
          (pairParentSystem baseSize depth).graph.Adj upper lower := by
        apply (ParentSystem.graph_adj_iff _ upper lower).mpr
        constructor
        · intro heq
          have hlevels := congrArg
            (fun x : PairVertex baseSize depth => x.1.val) heq
          change i + 1 = i at hlevels
          omega
        · left
          change lower ∈ pairParents baseSize depth upper
          change lower ∈
            v.val.map (pairLayerEmbedding baseSize depth i (by omega))
          exact Finset.mem_map.mpr ⟨parent, hparent, rfl⟩
      obtain ⟨a, ha⟩ := ih (by omega) parent
      refine ⟨a, hedge.reachable.trans ?_⟩
      exact ha
end TwoDegenerateGraphs
