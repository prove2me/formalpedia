-- Prove2me | solution 2 for WilliamsonShmoys.exists_plane_euler_data_supergraph_of_drawing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:25:37.67129+00:00
-- url     : https://prove2.me/submissions/2a017551-a43a-49c7-a820-661eb799ac4a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_PlaneEulerData
import Theorems.Thm_WilliamsonShmoys_connected_planar_supergraph_of_drawing_of_card_ge_three
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
    WilliamsonShmoys.connected_planar_supergraph_of_drawing_of_card_ge_three J hJ hV
  obtain ⟨L, hKL, hLdraw, hEL⟩ :=
    WilliamsonShmoys.triangulated_supergraph_of_connected_drawing K hKdraw hKconn hV
  exact ⟨L, hJK.trans hKL,
    WilliamsonShmoys.plane_euler_data_of_edge_formula L hV hEL⟩