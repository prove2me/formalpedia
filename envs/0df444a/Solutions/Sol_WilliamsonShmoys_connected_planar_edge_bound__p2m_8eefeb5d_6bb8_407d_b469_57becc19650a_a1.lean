-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound__p2m_8eefeb5d_6bb8_407d_b469_57becc19650a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:57:45.486959+00:00
-- url     : https://prove2.me/submissions/8babfd58-849b-4980-9a85-84a9eabb41b5

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_upper_bound__p2m_b5935805_1780_4fdc_8b62_9214cd276435_a2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hConnected : G.Connected)
    (hG : HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj;
      G.edgeFinset.card + 6 <= 3 * Fintype.card V) :=
  WilliamsonShmoys.maximal_planar_edge_upper_bound__p2m_b5935805_1780_4fdc_8b62_9214cd276435_a2 G hG hcard