-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_edge_count_upper_bound_ws
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T14:23:20.070991+00:00
-- url     : https://prove2.me/submissions/57001d68-364c-4c2d-b8c4-0a055732e052

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_v2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    M.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨N, _hMN, _hN, hle, hEq⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension_v2 M hV hM
  omega