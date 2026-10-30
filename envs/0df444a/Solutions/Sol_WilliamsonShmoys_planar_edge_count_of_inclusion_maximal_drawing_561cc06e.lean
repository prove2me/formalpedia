-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_of_inclusion_maximal_drawing_561cc06e
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T05:02:13.938723+00:00
-- url     : https://prove2.me/submissions/07c7396b-57b9-43eb-b560-55377215ea60

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_job_09cd0f78_596e_4a94_9326_038b3be8d638
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_lower_bound_of_inclusion_maximal_job_09cd0f78_596e_4a94_9326_038b3be8d638

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V)
    (hmax : forall M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M ->
      Set.Subset L.edgeSet M.edgeSet ->
      L.edgeSet = M.edgeSet) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper := WilliamsonShmoys.planar_edge_count_upper_bound_job_09cd0f78_596e_4a94_9326_038b3be8d638
    L hL hV
  have hlower := WilliamsonShmoys.planar_edge_count_lower_bound_of_inclusion_maximal_job_09cd0f78_596e_4a94_9326_038b3be8d638
    L hL hV hmax
  omega