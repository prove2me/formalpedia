-- Prove2me | solution 1 for SimpleGraph.euler_from_edge_increments__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:12:18.420171+00:00
-- url     : https://prove2.me/submissions/87f9a96a-532f-44a4-9957-86b7b18a0c22

import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card
import Theorems.Thm_SimpleGraph_preserved_by_edge_increments__p2m_c35c2347_1f47_4fca_afd1_0d99ec32a12f_a2
import Theorems.Thm_SimpleGraph_euler_identity_from_edge_increments__p2m_c35c2347_1f47_4fca_afd1_0d99ec32a12f_a2

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (P : SimpleGraph V → Prop)
    (f : SimpleGraph V → ℕ)
    (hzero : P ⊥ ∧ f ⊥ = 1)
    (hadd : ∀ (H : SimpleGraph V), H ≤ G →
      ∀ u v : V, u < v → G.Adj u v → ¬ H.Adj u v →
      P H →
        P (H ⊔ SimpleGraph.edge u v) ∧
        (H.Reachable u v →
          f (H ⊔ SimpleGraph.edge u v) = f H + 1) ∧
        (¬ H.Reachable u v →
          f (H ⊔ SimpleGraph.edge u v) = f H)) :
    P G ∧
      Fintype.card V + f G =
        G.edgeSet.ncard + Nat.card G.ConnectedComponent + 1 := by
  constructor
  · exact SimpleGraph.preserved_by_edge_increments__p2m_c35c2347_1f47_4fca_afd1_0d99ec32a12f_a2
      G P f hzero hadd
  · exact SimpleGraph.euler_identity_from_edge_increments__p2m_c35c2347_1f47_4fca_afd1_0d99ec32a12f_a2
      G P f hzero hadd
