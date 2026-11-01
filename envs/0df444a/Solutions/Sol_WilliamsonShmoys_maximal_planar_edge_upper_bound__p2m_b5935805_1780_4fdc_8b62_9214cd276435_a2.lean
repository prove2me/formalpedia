-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_upper_bound__p2m_b5935805_1780_4fdc_8b62_9214cd276435_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:19:18.794668+00:00
-- url     : https://prove2.me/submissions/a3ae0da6-948d-49c0-887d-757f0dd655ce
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_connected_planar_supergraph__p2m_8eefeb5d_6bb8_407d_b469_57becc19650a_a1
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_8eefeb5d_6bb8_407d_b469_57becc19650a_a1
import Theorems.Thm_WilliamsonShmoys_planar_edgeFinset_card_mono__p2m_8eefeb5d_6bb8_407d_b469_57becc19650a_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj;
      G.edgeFinset.card + 6 <= 3 * Fintype.card V) := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  obtain ⟨H, hGH, hConnected, hDrawing⟩ :=
    WilliamsonShmoys.planar_drawing_has_connected_planar_supergraph__p2m_8eefeb5d_6bb8_407d_b469_57becc19650a_a1 G hG
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  have hBound := WilliamsonShmoys.connected_planar_edge_bound__p2m_8eefeb5d_6bb8_407d_b469_57becc19650a_a1 H hConnected hDrawing hcard
  have hMono := WilliamsonShmoys.planar_edgeFinset_card_mono__p2m_8eefeb5d_6bb8_407d_b469_57becc19650a_a1 G H hGH
  omega