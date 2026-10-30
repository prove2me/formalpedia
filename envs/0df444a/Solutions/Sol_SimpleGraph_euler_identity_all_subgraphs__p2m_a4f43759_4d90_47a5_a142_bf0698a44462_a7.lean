-- Prove2me | solution 1 for SimpleGraph.euler_identity_all_subgraphs__p2m_a4f43759_4d90_47a5_a142_bf0698a44462_a7
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:27:10.558535+00:00
-- url     : https://prove2.me/submissions/6bce3dcb-a9aa-4719-8457-7231b2fbc44e

import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card
import Theorems.Thm_finite_edge_insertion_closure__p2m_32fb842e_c5cc_4fb3_a16d_c8f1f928ca75_a2
import Theorems.Thm_edge_insert_count_changes__p2m_32fb842e_c5cc_4fb3_a16d_c8f1f928ca75_a2
import Theorems.Thm_empty_graph_component_count__p2m_32fb842e_c5cc_4fb3_a16d_c8f1f928ca75_a2

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (P : SimpleGraph V → Prop)
    (f : SimpleGraph V → ℕ)
    (hzero : P ⊥ ∧ f ⊥ = 1)
    (hadd : ∀ (K : SimpleGraph V), K ≤ G →
      ∀ u v : V, u < v → G.Adj u v → ¬ K.Adj u v →
      P K →
        P (K ⊔ SimpleGraph.edge u v) ∧
        (K.Reachable u v → f (K ⊔ SimpleGraph.edge u v) = f K + 1) ∧
        (¬ K.Reachable u v → f (K ⊔ SimpleGraph.edge u v) = f K))
    (H : SimpleGraph V) (hHG : H ≤ G) :
    Fintype.card V + f H =
      H.edgeSet.ncard + Nat.card H.ConnectedComponent + 1 := by
  let Q : SimpleGraph V → Prop := fun K =>
    P K ∧ Fintype.card V + f K =
      K.edgeSet.ncard + Nat.card K.ConnectedComponent + 1
  have hbase : Q ⊥ := by
    refine ⟨hzero.1, ?_⟩
    rw [hzero.2, empty_graph_component_count__p2m_32fb842e_c5cc_4fb3_a16d_c8f1f928ca75_a2]
    simp
  have hstep : ∀ (K : SimpleGraph V), K ≤ G →
      ∀ u v : V, u < v → G.Adj u v → ¬ K.Adj u v →
      Q K → Q (K ⊔ SimpleGraph.edge u v) := by
    intro K hK u v huv hadj hnot hQ
    rcases hadd K hK u v huv hadj hnot hQ.1 with ⟨hP, hfReach, hfNReach⟩
    rcases edge_insert_count_changes__p2m_32fb842e_c5cc_4fb3_a16d_c8f1f928ca75_a2
      G K hK u v huv hadj hnot with ⟨hedge, hcompReach, hcompNReach⟩
    have hInv : Fintype.card V + f K =
        K.edgeSet.ncard + Nat.card K.ConnectedComponent + 1 := hQ.2
    refine ⟨hP, ?_⟩
    by_cases hreach : K.Reachable u v
    · have hF := hfReach hreach
      have hC := hcompReach hreach
      omega
    · have hF := hfNReach hreach
      have hC := hcompNReach hreach
      omega
  have hQH := finite_edge_insertion_closure__p2m_32fb842e_c5cc_4fb3_a16d_c8f1f928ca75_a2
    G Q hbase hstep H hHG
  exact hQH.2