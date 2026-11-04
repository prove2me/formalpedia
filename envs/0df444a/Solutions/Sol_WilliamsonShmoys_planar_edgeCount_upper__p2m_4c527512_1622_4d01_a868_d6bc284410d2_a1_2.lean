-- Prove2me | solution 2 for WilliamsonShmoys.planar_edgeCount_upper__p2m_4c527512_1622_4d01_a868_d6bc284410d2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:25:43.3432+00:00
-- url     : https://prove2.me/submissions/61c4dba7-9e39-434d-b9e2-38d45f7ce720

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edgeCount_upper_connected__p2m_4d9d61b3_a3d4_4adb_a77f_fb6a2cb8e8dc_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph_of_three_vertices__p2m_4d9d61b3_a3d4_4adb_a77f_fb6a2cb8e8dc_a2
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hn : 3 ≤ Fintype.card V) :
    K.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  classical
  obtain ⟨H, hKH, hHconn, hHdraw⟩ :=
    WilliamsonShmoys.planar_drawing_connected_supergraph_of_three_vertices__p2m_4d9d61b3_a3d4_4adb_a77f_fb6a2cb8e8dc_a2
      K hK hn
  have hcard : K.edgeFinset.card ≤ H.edgeFinset.card :=
    Finset.card_le_card (SimpleGraph.edgeFinset_mono hKH)
  exact hcard.trans
    (WilliamsonShmoys.planar_edgeCount_upper_connected__p2m_4d9d61b3_a3d4_4adb_a77f_fb6a2cb8e8dc_a1
      H hHdraw hHconn hn)
