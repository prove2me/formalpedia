-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_count_upper__p2m_1d31a56b_8574_4be9_a710_fc2e7a582d14_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:14:51.218201+00:00
-- url     : https://prove2.me/submissions/95d41c79-6f25-4593-93b5-9cca23370ba7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_8555a31b_9435_47a6_94cc_80670b8cc7a7_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_completion__p2m_8555a31b_9435_47a6_94cc_80670b8cc7a7_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hKH, hHconn, hHdraw⟩ :=
    WilliamsonShmoys.planar_drawing_connected_completion__p2m_8555a31b_9435_47a6_94cc_80670b8cc7a7_a2
      K hcard hK
  have hHbound :=
    WilliamsonShmoys.connected_planar_edge_bound__p2m_8555a31b_9435_47a6_94cc_80670b8cc7a7_a1
      H hcard hHconn hHdraw
  exact (Set.ncard_mono (SimpleGraph.edgeSet_mono hKH)).trans hHbound