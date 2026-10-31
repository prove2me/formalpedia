-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_08a17077_59d5_43fa_bc2a_526ccd70f8a2_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:56:16.415596+00:00
-- url     : https://prove2.me/submissions/39200ba0-41bd-4c22-b98e-b910c7456ea7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_014b5904_580f_46f1_bfdb_710877e74ec0_a1
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_014b5904_580f_46f1_bfdb_710877e74ec0_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : HasPlanarDrawingOn H) : H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨G, hsub, hconn, hdraw, hcard⟩ :=
    WilliamsonShmoys.planar_drawing_connected_extension__p2m_014b5904_580f_46f1_bfdb_710877e74ec0_a1
      H hV hH
  have hbound :=
    WilliamsonShmoys.connected_planar_edge_bound__p2m_014b5904_580f_46f1_bfdb_710877e74ec0_a1
      G hV hconn hdraw
  exact hcard.trans hbound