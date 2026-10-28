-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_exact_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T10:45:28.701479+00:00
-- url     : https://prove2.me/submissions/735321e9-c21e-4e46-bb23-6baff9082f8b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_for_maximal_exact_count
import Theorems.Thm_WilliamsonShmoys_planar_augmentation_lower_bound_for_maximal_exact_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hmax : ∀ K : SimpleGraph V,
      J ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = J) :
    J.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper :=
    WilliamsonShmoys.planar_drawing_edge_bound_for_maximal_exact_count J hV hJ
  have hlower :=
    WilliamsonShmoys.planar_augmentation_lower_bound_for_maximal_exact_count
      J hV hJ hmax
  omega