-- Prove2me | solution 1 for WilliamsonShmoys.exists_connected_planar_supergraph__p2m_5587bd77_cdbe_4d4a_9ac4_bb8e9f059500_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:04:51.842216+00:00
-- url     : https://prove2.me/submissions/5aa99b66-78b8-4de2-b5da-904128c2a696
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_bridge_extension__p2m_711af4b4_5214_45eb_bc71_e82c24cc238b_a2
import Theorems.Thm_WilliamsonShmoys_planar_bridge_iteration__p2m_711af4b4_5214_45eb_bc71_e82c24cc238b_a2

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 <= Fintype.card V) :
    Exists fun P : SimpleGraph V =>
      N <= P /\ P.Connected /\ WilliamsonShmoys.HasPlanarDrawingOn P := by
  exact WilliamsonShmoys.planar_bridge_iteration__p2m_711af4b4_5214_45eb_bc71_e82c24cc238b_a2
    (fun G hG hdisconnected =>
      WilliamsonShmoys.planar_drawing_bridge_extension__p2m_711af4b4_5214_45eb_bc71_e82c24cc238b_a2
        G hG hdisconnected)
    N hN hcard