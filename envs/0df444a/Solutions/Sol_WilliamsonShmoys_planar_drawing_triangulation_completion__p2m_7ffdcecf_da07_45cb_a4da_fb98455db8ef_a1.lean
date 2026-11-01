-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_completion__p2m_7ffdcecf_da07_45cb_a4da_fb98455db8ef_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:53:08.492495+00:00
-- url     : https://prove2.me/submissions/1e9815fb-ef95-4a7f-8528-f90b8905a0a9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_exists__p2m_05876c00_4f7e_4d9e_b91e_0da976d19dc6_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_05876c00_4f7e_4d9e_b91e_0da976d19dc6_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    exists L : SimpleGraph V,
      (forall u v, G.Adj u v -> L.Adj u v) /\
      WilliamsonShmoys.HasPlanarDrawingOn L /\
      3 * Fintype.card V = L.edgeSet.ncard + 6 := by
  obtain ⟨L, hGL, hL, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph_exists__p2m_05876c00_4f7e_4d9e_b91e_0da976d19dc6_a1
      G hG
  exact ⟨L, hGL, hL,
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_05876c00_4f7e_4d9e_b91e_0da976d19dc6_a1
      L hL hcard hmax⟩