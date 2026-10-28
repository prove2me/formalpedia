-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_euler_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T18:19:17.964231+00:00
-- url     : https://prove2.me/submissions/d1e04d46-cedf-40c5-8ead-69a526592a33
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_for_maximal_planar_edge_count_euler_v2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_for_maximal_planar_edge_count_euler_v2

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper :=
    WilliamsonShmoys.planar_edge_count_upper_bound_for_maximal_planar_edge_count_euler_v2
      H hH hCard
  have hLower :=
    WilliamsonShmoys.maximal_planar_edge_count_lower_bound_for_maximal_planar_edge_count_euler_v2
      H hH hmax hCard
  omega