-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound__p2m_9fdf65a3_2cbf_4cec_9951_ee8b977e74bf_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:16:37.944421+00:00
-- url     : https://prove2.me/submissions/180a5c4f-e82e-4d1a-8dfe-83f69d67f335
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_maximal_extension__p2m_71de413d_a2cb_43c4_9595_c6ba34d7c93b_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_71de413d_a2cb_43c4_9595_c6ba34d7c93b_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨H, hGH, hCardMono, hDrawH, hMax⟩ :=
    WilliamsonShmoys.planar_graph_maximal_extension__p2m_71de413d_a2cb_43c4_9595_c6ba34d7c93b_a1
      G hDraw hV
  have hCount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_71de413d_a2cb_43c4_9595_c6ba34d7c93b_a1
      H hMax hV
  omega