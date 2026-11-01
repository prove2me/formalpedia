-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_022fc3fe_2112_4838_9b2a_056c25ecda08_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:48:30.440362+00:00
-- url     : https://prove2.me/submissions/e5c53205-59ec-449a-be3a-83a409e81d0c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_maximal_planar_supergraph__p2m_40c1c52c_c498_4287_a557_1efecd0d6ca7_a3
import Theorems.Thm_WilliamsonShmoys_subgraph_of_maximal_planar_drawing_obeys_edge_bound__p2m_40c1c52c_c498_4287_a557_1efecd0d6ca7_a3
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hcard : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeFinset.card + 6 <= 3 * Fintype.card V := by
  classical
  letI : DecidableRel G.Adj := dG
  obtain ⟨H, hsub, hH, hmax⟩ :=
    WilliamsonShmoys.drawable_graph_has_maximal_planar_supergraph__p2m_40c1c52c_c498_4287_a557_1efecd0d6ca7_a3
      G hcard hG
  exact WilliamsonShmoys.subgraph_of_maximal_planar_drawing_obeys_edge_bound__p2m_40c1c52c_c498_4287_a557_1efecd0d6ca7_a3
    G H hcard hsub hH hmax