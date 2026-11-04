-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_edge_bound__p2m_f41edfa3_d13d_40ca_8475_768212b4c7c0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:12:54.945278+00:00
-- url     : https://prove2.me/submissions/d94b936d-e408-445f-a3d0-616241ab6837

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_52d80640_fd16_42f7_b63d_2010f98eda2f_a1
import Theorems.Thm_WilliamsonShmoys_connect_planar_drawing__p2m_52d80640_fd16_42f7_b63d_2010f98eda2f_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
      K.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  classical
  obtain ⟨H, hKH, hHconn, hHdraw⟩ :=
    WilliamsonShmoys.connect_planar_drawing__p2m_52d80640_fd16_42f7_b63d_2010f98eda2f_a1
      K hV hK
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  have hbound :=
    WilliamsonShmoys.connected_planar_edge_bound__p2m_52d80640_fd16_42f7_b63d_2010f98eda2f_a1
      H hV hHconn hHdraw
  have hcard : K.edgeFinset.card ≤ H.edgeFinset.card :=
    Finset.card_le_card (SimpleGraph.edgeFinset_mono hKH)
  exact Nat.le_trans (Nat.add_le_add_right hcard 6) hbound