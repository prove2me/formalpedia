-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawing_edge_bound__p2m_7e15a8d6_7041_4a6f_b660_410e45ab60c6_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:31:35.668313+00:00
-- url     : https://prove2.me/submissions/c370c14e-10c3-444a-8feb-bc7746812ec0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawing_edge_bound_connected__p2m_af29040b_5f5f_41c7_ae26_98a3e427e1bc_a1
import Theorems.Thm_WilliamsonShmoys_planarDrawing_connect_components__p2m_af29040b_5f5f_41c7_ae26_98a3e427e1bc_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) + 6 ≤ 3 * Fintype.card V := by
  classical
  obtain ⟨H, dH, hGH, hConn, hPlanar, hCardMono⟩ :=
    WilliamsonShmoys.planarDrawing_connect_components__p2m_af29040b_5f5f_41c7_ae26_98a3e427e1bc_a1
      G dG hG
  have hBound :=
    WilliamsonShmoys.planarDrawing_edge_bound_connected__p2m_af29040b_5f5f_41c7_ae26_98a3e427e1bc_a1
      H dH hPlanar hConn hcard
  omega