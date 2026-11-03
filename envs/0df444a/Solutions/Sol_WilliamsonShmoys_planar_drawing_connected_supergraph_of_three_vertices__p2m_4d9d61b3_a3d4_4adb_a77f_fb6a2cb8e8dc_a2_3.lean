-- Prove2me | solution 3 for WilliamsonShmoys.planar_drawing_connected_supergraph_of_three_vertices__p2m_4d9d61b3_a3d4_4adb_a77f_fb6a2cb8e8dc_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T22:21:10.132798+00:00
-- url     : https://prove2.me/submissions/74ea08d9-2822-4df7-8205-f19b7c7756e7

import Theorems.Thm_WilliamsonShmoys_connect_planar_drawing__p2m_52d80640_fd16_42f7_b63d_2010f98eda2f_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hn : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H :=
  WilliamsonShmoys.connect_planar_drawing__p2m_52d80640_fd16_42f7_b63d_2010f98eda2f_a1 K hn hK