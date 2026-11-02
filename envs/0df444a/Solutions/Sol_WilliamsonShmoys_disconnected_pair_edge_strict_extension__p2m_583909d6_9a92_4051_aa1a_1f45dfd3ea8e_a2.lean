-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_pair_edge_strict_extension__p2m_583909d6_9a92_4051_aa1a_1f45dfd3ea8e_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:50:32.585208+00:00
-- url     : https://prove2.me/submissions/1b7e1f6d-60bd-4772-a5df-04b95c6a440b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hDisconnected : ¬ H.Connected)
    (hn : Nat.le 3 (Fintype.card V)) :
    ∃ u v : V,
      ¬ H.Reachable u v ∧
      H ≤ H ⊔ SimpleGraph.edge u v ∧
      H ≠ H ⊔ SimpleGraph.edge u v := by
  classical
  have hpair : ∃ u v : V, ¬ H.Reachable u v := by
    by_contra hNoPair
    apply hDisconnected
    rw [SimpleGraph.connected_iff]
    constructor
    · intro u v
      by_contra hNotReachable
      exact hNoPair ⟨u, v, hNotReachable⟩
    · have hpos : 0 < Fintype.card V := lt_of_lt_of_le (by decide : 0 < 3) hn
      exact (Fintype.card_pos_iff).mp hpos
  obtain ⟨u, v, huv⟩ := hpair
  have huv_ne : u ≠ v := by
    intro heq
    subst v
    exact huv (by simp)
  refine ⟨u, v, huv, le_sup_left, ?_⟩
  intro heq
  have hadj : (H ⊔ SimpleGraph.edge u v).Adj u v := by
    simp [SimpleGraph.edge_adj, huv_ne]
  have hreach : (H ⊔ SimpleGraph.edge u v).Reachable u v := hadj.reachable
  apply huv
  rw [← heq] at hreach
  exact hreach