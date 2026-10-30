-- Prove2me | solution 1 for SimpleGraph.preserved_by_edge_increments__p2m_c35c2347_1f47_4fca_afd1_0d99ec32a12f_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:18:19.897259+00:00
-- url     : https://prove2.me/submissions/8ef87e26-f012-44c5-85f5-0c32cb40399a

import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card
import Theorems.Thm_SimpleGraph_exists_ordered_edge_list__p2m_7e139eb9_902e_43ae_a2cc_5a720eb5726b_a2
import Theorems.Thm_SimpleGraph_buildEdgeList_preserves__p2m_7e139eb9_902e_43ae_a2cc_5a720eb5726b_a2

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (P : SimpleGraph V → Prop)
    (f : SimpleGraph V → ℕ)
    (hzero : P ⊥ ∧ f ⊥ = 1)
    (hadd : ∀ (H : SimpleGraph V), H ≤ G →
      ∀ u v : V, u < v → G.Adj u v → ¬ H.Adj u v →
      P H →
        P (H ⊔ SimpleGraph.edge u v) ∧
        (H.Reachable u v → f (H ⊔ SimpleGraph.edge u v) = f H + 1) ∧
        (¬ H.Reachable u v → f (H ⊔ SimpleGraph.edge u v) = f H)) :
    P G := by
  classical
  obtain ⟨es, hes, hbuild⟩ :=
    SimpleGraph.exists_ordered_edge_list__p2m_7e139eb9_902e_43ae_a2cc_5a720eb5726b_a2 G
  rw [← hbuild]
  exact SimpleGraph.buildEdgeList_preserves__p2m_7e139eb9_902e_43ae_a2cc_5a720eb5726b_a2
    G P hzero.1
    (fun H hHG u v huv hadj hnot hP => (hadd H hHG u v huv hadj hnot hP).1)
    ⊥ bot_le hzero.1 es hes