-- Prove2me | solution 1 for WilliamsonShmoys.connected_graph_edge_bound_small__p2m_2921e68e_aa42_4dea_8127_751b3e371ec8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:57:24.718613+00:00
-- url     : https://prove2.me/submissions/6da4cab5-b512-4616-b7f5-7e0dfd66b659

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hconn : G.Connected)
    (hcard : Fintype.card V < 3) :
    (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) + 3 ≤ 3 * Fintype.card V := by
  letI : DecidableRel G.Adj := dG
  classical
  change G.edgeFinset.card + 3 ≤ 3 * Fintype.card V
  have hpos : 0 < Fintype.card V :=
    Fintype.card_pos_iff.mpr ⟨hconn.nonempty.some⟩
  have hedge : G.edgeFinset.card ≤ (Fintype.card V).choose 2 :=
    SimpleGraph.card_edgeFinset_le_card_choose_two
  have hsize : Fintype.card V = 1 ∨ Fintype.card V = 2 := by omega
  rcases hsize with hsize | hsize
  · have hedge' : G.edgeFinset.card ≤ 0 := by
      simpa [hsize] using hedge
    rw [hsize]
    omega
  · have hedge' : G.edgeFinset.card ≤ 1 := by
      simpa [hsize] using hedge
    rw [hsize]
    omega