-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_c4d63dfe_c88f_43bb_a642_10d75b5a8453_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:21:06.970404+00:00
-- url     : https://prove2.me/submissions/81842ba4-ce80-45fd-811c-7906bdaee39a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_data__p2m_7d4137c4_15dc_451a_ba6d_47dc1f35dd68_a1
import Theorems.Thm_WilliamsonShmoys_planar_face_data_edge_bound__p2m_7d4137c4_15dc_451a_ba6d_47dc1f35dd68_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨f, boundary, heuler, htotal, hface⟩ :=
    WilliamsonShmoys.planar_drawing_face_data__p2m_7d4137c4_15dc_451a_ba6d_47dc1f35dd68_a1
      K hcard hconn hK
  exact WilliamsonShmoys.planar_face_data_edge_bound__p2m_7d4137c4_15dc_451a_ba6d_47dc1f35dd68_a1
    (Fintype.card V) K.edgeSet.ncard f boundary hcard heuler htotal hface
