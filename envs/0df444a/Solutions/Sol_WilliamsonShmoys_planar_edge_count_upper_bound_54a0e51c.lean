-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound_54a0e51c
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T22:59:46.324492+00:00
-- url     : https://prove2.me/submissions/5f656c39-773c-4200-a3d3-20877a711be8

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_drawing_extension__p2m_0ef6cdd6_0074_4ddf_9918_5e48acac88b4_a3
import Theorems.Thm_WilliamsonShmoys_edge_count_upper_bound_of_maximal_planar_drawing__p2m_0ef6cdd6_0074_4ddf_9918_5e48acac88b4_a3

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨H, hGH, hcard, hPlanarH, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_drawing_extension__p2m_0ef6cdd6_0074_4ddf_9918_5e48acac88b4_a3 G hG
  have hBound :=
    WilliamsonShmoys.edge_count_upper_bound_of_maximal_planar_drawing__p2m_0ef6cdd6_0074_4ddf_9918_5e48acac88b4_a3
      H hV hPlanarH hmax
  omega