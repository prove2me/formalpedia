-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound__p2m_50304f69_3f87_43f6_91bb_4f1f44440925_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:59:10.538521+00:00
-- url     : https://prove2.me/submissions/75688683-9f49-4791-86bd-aed20eb50c34
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound__p2m_2ba654e2_e4e9_4dba_a1f5_978037f8b005_a2
import Theorems.Thm_WilliamsonShmoys_connect_planar_drawing__p2m_2ba654e2_e4e9_4dba_a1f5_978037f8b005_a2

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V) (hDraw : HasPlanarDrawingOn S)
    (hV : 3 <= Fintype.card V) :
    S.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨T, hEdges, hTDraw, hTConnected⟩ :=
    WilliamsonShmoys.connect_planar_drawing__p2m_2ba654e2_e4e9_4dba_a1f5_978037f8b005_a2
      S hDraw hV
  calc
    S.edgeSet.ncard <= T.edgeSet.ncard := hEdges
    _ <= 3 * Fintype.card V - 6 :=
      WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_2ba654e2_e4e9_4dba_a1f5_978037f8b005_a2
        T hTDraw hTConnected hV
