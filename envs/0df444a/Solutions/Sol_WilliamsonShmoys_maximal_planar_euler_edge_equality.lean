-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_euler_edge_equality
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T19:55:54.215927+00:00
-- url     : https://prove2.me/submissions/14d1107a-0db2-4aee-ba37-74d49d984e7e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound_c76468fe
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_c76468fe

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hCard : 3 ≤ Fintype.card V) : H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hu := WilliamsonShmoys.planar_edge_upper_bound_c76468fe H hH hCard
  have hl := WilliamsonShmoys.maximal_planar_edge_lower_bound_c76468fe H hH hmax hCard
  omega