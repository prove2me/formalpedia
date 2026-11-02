-- Prove2me | solution 1 for WilliamsonShmoys.inclusion_maximal_planar_drawing_has_three_n_minus_six_edges__p2m_6f695848_ebe7_49d1_9027_cfad81c2f288_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:26:58.023772+00:00
-- url     : https://prove2.me/submissions/9795c574-d106-408b-94b6-0b7b5bcca3bd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_supergraph_with_exact_edge_count__p2m_b7da0b5c_b8e2_42e5_8f2d_d77c61d3fb07_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hmax : ∀ Q : SimpleGraph V, P ≤ Q → WilliamsonShmoys.HasPlanarDrawingOn Q → Q = P)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel P.Adj := Classical.decRel P.Adj
    3 * Fintype.card V = P.edgeFinset.card + 6 := by
  letI : DecidableRel P.Adj := Classical.decRel P.Adj
  obtain ⟨Q, hPQ, hQ, hcount⟩ :=
    WilliamsonShmoys.planar_graph_has_triangulated_supergraph_with_exact_edge_count__p2m_b7da0b5c_b8e2_42e5_8f2d_d77c61d3fb07_a1 P hP hcard
  have hQP : Q = P := hmax Q hPQ hQ
  subst Q
  exact hcount