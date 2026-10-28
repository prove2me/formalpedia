-- Prove2me | solution 1 for WilliamsonShmoys.exists_plane_euler_data_supergraph_of_drawing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:11:40.723996+00:00
-- url     : https://prove2.me/submissions/5a813e38-3088-46d9-8c3b-c84a50d4d2d0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_PlaneEulerData
import Theorems.Thm_WilliamsonShmoys_connected_planar_supergraph_of_drawing
import Theorems.Thm_WilliamsonShmoys_triangulated_supergraph_of_connected_drawing
import Theorems.Thm_WilliamsonShmoys_plane_euler_data_of_edge_formula

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      J.edgeSet ⊆ K.edgeSet ∧ WilliamsonShmoys.HasPlaneEulerData K := by
  obtain ⟨K, hJK, hKdraw, hKconn⟩ :=
    WilliamsonShmoys.connected_planar_supergraph_of_drawing J hJ
  obtain ⟨L, hKL, hLdraw, hEL⟩ :=
    WilliamsonShmoys.triangulated_supergraph_of_connected_drawing K hKdraw hKconn hV
  exact ⟨L, hJK.trans hKL,
    WilliamsonShmoys.plane_euler_data_of_edge_formula L hV hEL⟩