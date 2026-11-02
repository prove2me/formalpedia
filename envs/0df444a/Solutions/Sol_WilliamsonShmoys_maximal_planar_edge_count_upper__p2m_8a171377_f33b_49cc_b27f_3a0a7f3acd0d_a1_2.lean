-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_8a171377_f33b_49cc_b27f_3a0a7f3acd0d_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:55:54.588871+00:00
-- url     : https://prove2.me/submissions/1fd80de6-80c8-46d7-9e01-999780c4780b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_f1cbd61d_56d2_4b64_81ce_1556811a8e35_a2
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_f1cbd61d_56d2_4b64_81ce_1556811a8e35_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hn : Nat.le 3 (Fintype.card V)) :
    Nat.le K.edgeFinset.card (3 * Fintype.card V - 6) := by
  classical
  obtain ⟨H, dH, hHconn, hHdraw, hcard⟩ :=
    WilliamsonShmoys.planar_drawing_connected_extension__p2m_f1cbd61d_56d2_4b64_81ce_1556811a8e35_a2
      K dK hK hn
  have hbound :=
    WilliamsonShmoys.connected_planar_edge_bound__p2m_f1cbd61d_56d2_4b64_81ce_1556811a8e35_a1
      H dH hHconn hHdraw hn
  exact Nat.le_trans hcard hbound