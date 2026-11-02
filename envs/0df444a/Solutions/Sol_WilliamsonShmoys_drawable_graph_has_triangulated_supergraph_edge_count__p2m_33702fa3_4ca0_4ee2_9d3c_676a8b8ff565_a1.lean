-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_has_triangulated_supergraph_edge_count__p2m_33702fa3_4ca0_4ee2_9d3c_676a8b8ff565_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:54:51.014701+00:00
-- url     : https://prove2.me/submissions/c29f8bc7-0336-4d0c-87ff-95751c55cf0f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_drawable_graph_has_maximal_drawable_extension__p2m_8b622a66_c72a_42ac_86d2_b24f5cfdd6f7_a1
import Theorems.Thm_maximal_drawable_graph_has_triangulated_edge_count__p2m_8b622a66_c72a_42ac_86d2_b24f5cfdd6f7_a1

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hn : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V, ∃ dK : DecidableRel K.Adj,
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      H ≤ K ∧
      (letI : DecidableRel K.Adj := dK;
       3 * Fintype.card V - 6 = K.edgeFinset.card) := by
  obtain ⟨K, hK, hHK, hmax⟩ :=
    drawable_graph_has_maximal_drawable_extension__p2m_8b622a66_c72a_42ac_86d2_b24f5cfdd6f7_a1 H hH
  obtain ⟨dK, hcard⟩ :=
    maximal_drawable_graph_has_triangulated_edge_count__p2m_8b622a66_c72a_42ac_86d2_b24f5cfdd6f7_a1 K hK hn hmax
  exact ⟨K, dK, hK, hHK, hcard⟩