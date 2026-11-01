-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound__p2m_3b70d152_dbfb_4f09_8d03_767be9da3cd3_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:54:42.666199+00:00
-- url     : https://prove2.me/submissions/a2a62b2b-9297-4985-abf6-27c9ff75ecb7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_components_connectible__p2m_ba06bb4d_e92b_4537_887e_0721c652813c_a3
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound__p2m_ba06bb4d_e92b_4537_887e_0721c652813c_a3

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hconn, hK, hedge⟩ :=
    WilliamsonShmoys.planar_drawing_components_connectible__p2m_ba06bb4d_e92b_4537_887e_0721c652813c_a3
      (V := V) H hcard hH
  have hbound :=
    WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_ba06bb4d_e92b_4537_887e_0721c652813c_a3
      (V := V) K hcard hconn hK
  omega