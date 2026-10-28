-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_exact
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T04:34:08.558909+00:00
-- url     : https://prove2.me/submissions/44c95623-5281-4def-ac8a-5810c3e5c144
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound_8742a5e4_f287_4b84_b71a_f78e094dd85c
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound_8742a5e4_f287_4b84_b71a_f78e094dd85c

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hMax : ∀ K : SimpleGraph V,
      J ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K = J) :
    J.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hUpper :=
    WilliamsonShmoys.planar_drawing_edge_count_upper_bound_8742a5e4_f287_4b84_b71a_f78e094dd85c
      J hV hJ
  have hLower :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound_8742a5e4_f287_4b84_b71a_f78e094dd85c
      J hV hJ hMax
  omega