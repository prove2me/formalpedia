-- Prove2me | solution 1 for OPG37271.subcubic_seven_color_of_bridgeless
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T04:48:12.665395+00:00
-- url     : https://prove2.me/submissions/f91bcb10-db5f-4735-b89c-b8026e2d4149
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_opg37271_star_edge_coloring
import Theorems.Thm_OPG37271_hasStarEdgeColoring_of_bridge
import Theorems.Thm_OPG37271_hasStarEdgeColoring_of_adj_deg_le_two
import Theorems.Thm_OPG37271_subcubic_seven_color_of_no_adj_deg_le_two
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Finset.Card

set_option autoImplicit false

open OPG37271

universe u

theorem solution {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hsubcubic : IsSubcubic G)
    (hbridgeless : ∀ u v : V, G.Adj u v → (G.deleteEdges {s(u, v)}).Reachable u v) :
    HasStarEdgeColoring G 7 := by
  classical
  have hstrong : ∀ (n : ℕ) (H : SimpleGraph V),
      H.edgeFinset.card = n → IsSubcubic H → HasStarEdgeColoring H 7 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro H hcard hsubH
      by_cases hbridge : ∃ u v : V, H.Adj u v ∧ ¬ (H.deleteEdges {s(u, v)}).Reachable u v
      · rcases hbridge with ⟨u, v, huv, hbr⟩
        let H' := H.deleteEdges {s(u, v)}
        have hH'le : H' ≤ H := SimpleGraph.deleteEdges_le {s(u, v)}
        have hsubH' : IsSubcubic H' :=
          fun w => le_trans (Set.encard_le_encard (SimpleGraph.neighborSet_mono hH'le w)) (hsubH w)
        have hlt : H'.edgeFinset.card < n := by
          rw [← hcard]
          apply Finset.card_lt_card
          rw [Finset.ssubset_iff_of_subset]
          · refine ⟨s(u, v), SimpleGraph.mem_edgeFinset.mpr huv, ?_⟩
            rw [SimpleGraph.mem_edgeFinset]
            intro hmem
            exact (SimpleGraph.deleteEdges_adj.mp hmem).2 rfl
          · intro e he
            rw [SimpleGraph.mem_edgeFinset] at he ⊢
            exact SimpleGraph.edgeSet_mono hH'le he
        have hc' : HasStarEdgeColoring H' 7 := ih _ (by convert hlt) H' (by convert rfl) hsubH'
        exact OPG37271.hasStarEdgeColoring_of_bridge hsubH u v huv hbr hc'
      · push Not at hbridge
        by_cases hadj2 : ∃ u v : V, H.Adj u v ∧ (H.neighborSet u).encard ≤ 2 ∧ (H.neighborSet v).encard ≤ 2
        · rcases hadj2 with ⟨u, v, huv, hu2, hv2⟩
          let H' := H.deleteEdges {s(u, v)}
          have hH'le : H' ≤ H := SimpleGraph.deleteEdges_le {s(u, v)}
          have hsubH' : IsSubcubic H' :=
            fun w => le_trans (Set.encard_le_encard (SimpleGraph.neighborSet_mono hH'le w)) (hsubH w)
          have hlt : H'.edgeFinset.card < n := by
            rw [← hcard]
            apply Finset.card_lt_card
            rw [Finset.ssubset_iff_of_subset]
            · refine ⟨s(u, v), SimpleGraph.mem_edgeFinset.mpr huv, ?_⟩
              rw [SimpleGraph.mem_edgeFinset]
              intro hmem
              exact (SimpleGraph.deleteEdges_adj.mp hmem).2 rfl
            · intro e he
              rw [SimpleGraph.mem_edgeFinset] at he ⊢
              exact SimpleGraph.edgeSet_mono hH'le he
          have hc' : HasStarEdgeColoring H' 7 := ih _ (by convert hlt) H' (by convert rfl) hsubH'
          exact OPG37271.hasStarEdgeColoring_of_adj_deg_le_two hsubH u v huv hu2 hv2 hc'
        · push Not at hadj2
          exact OPG37271.subcubic_seven_color_of_no_adj_deg_le_two H hsubH hbridge (fun u v huv h => not_le.mpr (hadj2 u v huv h.1) h.2)
  exact hstrong G.edgeFinset.card G rfl hsubcubic
