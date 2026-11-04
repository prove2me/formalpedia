-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_with_few_edges_has_proper_drawable_extension__p2m_cec667e7_b432_426e_9cef_b901d387a12d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-03T16:34:48.479472+00:00
-- url     : https://prove2.me/submissions/0c5d88b5-b295-41a7-9f6b-faa6a73d1080

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulated_extension_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hE : K.edgeFinset.card < 3 * Fintype.card V - 6) :
    ∃ (L : SimpleGraph V) (hLdec : DecidableRel L.Adj),
      (∀ {u v}, K.Adj u v → L.Adj u v) ∧
      (∃ u v, L.Adj u v ∧ ¬ K.Adj u v) ∧
      HasPlanarDrawingOn L := by
  classical
  obtain ⟨L, hKL, hL, hcard⟩ :=
    planar_drawing_triangulated_extension_edge_count K hK hV
  have hne : K ≠ L := by
    intro heq
    subst L
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset] at hcard
    omega
  have hextra : ∃ u v, L.Adj u v ∧ ¬ K.Adj u v := by
    by_contra hn
    push_neg at hn
    have hLK : L ≤ K := by
      intro u v huv
      exact hn u v huv
    exact hne (le_antisymm hKL hLK)
  exact ⟨L, Classical.decRel L.Adj, fun h => hKL h, hextra, hL⟩
