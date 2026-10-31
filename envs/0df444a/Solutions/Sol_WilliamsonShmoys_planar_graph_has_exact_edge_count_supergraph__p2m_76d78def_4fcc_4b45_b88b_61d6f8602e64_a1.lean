-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_exact_edge_count_supergraph__p2m_76d78def_4fcc_4b45_b88b_61d6f8602e64_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:54:57.850975+00:00
-- url     : https://prove2.me/submissions/3d8c7742-3b0f-4963-86ba-0c8fd46fdfe9

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph__p2m_49d536b5_943b_4c07_ac34_73c598814091_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_49d536b5_943b_4c07_ac34_73c598814091_a1
set_option autoImplicit false
open WilliamsonShmoys
theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V) (hDraw : HasPlanarDrawingOn S)
    (hV : 3 <= Fintype.card V) :
    ∃ T : SimpleGraph V, S <= T ∧ HasPlanarDrawingOn T ∧
      3 * Fintype.card V - 6 = T.edgeSet.ncard := by
  obtain ⟨T, hST, hTDraw, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_49d536b5_943b_4c07_ac34_73c598814091_a1
      S hDraw
  have hCount :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_49d536b5_943b_4c07_ac34_73c598814091_a1
      T hTDraw hV hMax
  refine ⟨T, hST, hTDraw, ?_⟩
  omega