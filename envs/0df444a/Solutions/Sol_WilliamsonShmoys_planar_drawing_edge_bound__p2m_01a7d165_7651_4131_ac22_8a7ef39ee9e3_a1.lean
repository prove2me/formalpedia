-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound__p2m_01a7d165_7651_4131_ac22_8a7ef39ee9e3_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:03:41.858395+00:00
-- url     : https://prove2.me/submissions/cf3b46f3-c6bb-467a-b92b-a390e65d5556
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_data__p2m_cb41be71_821a_4ee1_8bbc_87748aa8233d_a1
import Theorems.Thm_WilliamsonShmoys_edge_bound_from_face_data__p2m_cb41be71_821a_4ee1_8bbc_87748aa8233d_a1
import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hconn : K.Connected) (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V) :
    K.edgeFinset.card + 6 <= 3 * Fintype.card V := by
  obtain ⟨f, heuler, hfaces⟩ :=
    WilliamsonShmoys.planar_drawing_face_data__p2m_cb41be71_821a_4ee1_8bbc_87748aa8233d_a1
      K dK hconn hK hcard
  exact WilliamsonShmoys.edge_bound_from_face_data__p2m_cb41be71_821a_4ee1_8bbc_87748aa8233d_a1
    (Fintype.card V) K.edgeFinset.card f heuler hfaces