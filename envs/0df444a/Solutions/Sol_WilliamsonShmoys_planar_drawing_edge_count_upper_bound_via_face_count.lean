-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_upper_bound_via_face_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T23:06:53.593362+00:00
-- url     : https://prove2.me/submissions/9c5ed1c0-5906-4c39-b196-51d6a60e9576
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_2c262075_af7a_40b5_8216_f56b847d81a6_a3
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_count__p2m_2c262075_af7a_40b5_8216_f56b847d81a6_a3

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    T.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hTH, hConn, hH⟩ :=
    WilliamsonShmoys.planar_drawing_connected_extension__p2m_2c262075_af7a_40b5_8216_f56b847d81a6_a3 T hV hT
  have hsub : T.edgeSet ⊆ H.edgeSet := SimpleGraph.edgeSet_mono hTH
  calc
    T.edgeSet.ncard ≤ H.edgeSet.ncard := Set.ncard_mono hsub
    _ ≤ 3 * Fintype.card V - 6 :=
      WilliamsonShmoys.connected_planar_drawing_edge_count__p2m_2c262075_af7a_40b5_8216_f56b847d81a6_a3 H hV hConn hH