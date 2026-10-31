-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_graph_edge_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T04:56:15.147628+00:00
-- url     : https://prove2.me/submissions/b2674e5b-f5aa-4c6a-b396-b1f08506812a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_with_edge_mono
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_count_euler_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    Y.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨Z, hYZ, hZconn, hZplanar, hmono⟩ :=
    WilliamsonShmoys.planar_drawing_connected_extension_with_edge_mono Y hV hY
  have hbound :=
    WilliamsonShmoys.connected_planar_drawing_edge_count_euler_bound
      Z hV hZconn hZplanar
  omega