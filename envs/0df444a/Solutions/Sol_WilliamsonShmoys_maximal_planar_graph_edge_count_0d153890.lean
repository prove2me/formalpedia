-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count_0d153890
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T09:48:13.17903+00:00
-- url     : https://prove2.me/submissions/cc829ab4-3d8f-4c3a-adda-0cfe24cc38b5

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_via_euler_1f8dbaa1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_via_triangulation_1f8dbaa1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall J : SimpleGraph V,
      H <= J -> WilliamsonShmoys.HasPlanarDrawingOn J -> J = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper :=
    WilliamsonShmoys.planar_edge_count_upper_via_euler_1f8dbaa1 H hV hH
  have hLower :=
    WilliamsonShmoys.maximal_planar_edge_count_lower_via_triangulation_1f8dbaa1
      H hV hH hmax
  omega
