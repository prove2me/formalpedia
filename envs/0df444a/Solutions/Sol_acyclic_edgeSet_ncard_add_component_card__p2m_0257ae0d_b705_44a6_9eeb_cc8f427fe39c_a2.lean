-- Prove2me | solution 1 for acyclic_edgeSet_ncard_add_component_card__p2m_0257ae0d_b705_44a6_9eeb_cc8f427fe39c_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:23:43.574254+00:00
-- url     : https://prove2.me/submissions/53dce5b2-bc63-4830-a923-885594961911

import Theorems.Thm_acyclic_components_tree_edge_formula__p2m_cd99b0ce_6168_4c6b_a6a6_0ae22062f109_a3
import Theorems.Thm_component_edge_partition_sum__p2m_cd99b0ce_6168_4c6b_a6a6_0ae22062f109_a3
import Theorems.Thm_component_vertex_partition_sum__p2m_cd99b0ce_6168_4c6b_a6a6_0ae22062f109_a3

open SimpleGraph

theorem solution {V : Type} [Fintype V] (G : SimpleGraph V) (hG : G.IsAcyclic) :
    G.edgeSet.ncard + Nat.card G.ConnectedComponent = Fintype.card V := by
  classical
  letI : Fintype G.ConnectedComponent := Fintype.ofFinite G.ConnectedComponent
  calc
    G.edgeSet.ncard + Nat.card G.ConnectedComponent =
        Finset.univ.sum (fun C : G.ConnectedComponent => C.toSimpleGraph.edgeSet.ncard + 1) :=
      component_edge_partition_sum__p2m_cd99b0ce_6168_4c6b_a6a6_0ae22062f109_a3 G
    _ = Finset.univ.sum (fun C : G.ConnectedComponent => Nat.card (C : Set V)) := by
      apply Finset.sum_congr rfl
      intro C hC
      exact acyclic_components_tree_edge_formula__p2m_cd99b0ce_6168_4c6b_a6a6_0ae22062f109_a3 G hG C
    _ = Fintype.card V :=
      component_vertex_partition_sum__p2m_cd99b0ce_6168_4c6b_a6a6_0ae22062f109_a3 G