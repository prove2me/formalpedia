-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_exact_edge_count_v3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T19:41:06.511549+00:00
-- url     : https://prove2.me/submissions/9fe3db84-850e-47a5-8a6d-a9a4bb9708ad
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound_v3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_v3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ H' : SimpleGraph V,
      H ≤ H' → WilliamsonShmoys.HasPlanarDrawingOn H' → H' = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.planar_edge_upper_bound_v3 H hH hCard
  have hLower := WilliamsonShmoys.maximal_planar_edge_lower_bound_v3 H hH hCard hMax
  omega