-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_eq_euler
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T19:01:35.147111+00:00
-- url     : https://prove2.me/submissions/ecd5ce47-c977-443f-90ca-bea9984c056d

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_eq_euler_upper_bound
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_eq_euler_lower_bound
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.maximal_planar_edge_count_eq_euler_upper_bound H hH hCard
  have hLower := WilliamsonShmoys.maximal_planar_edge_count_eq_euler_lower_bound H hH hmax hCard
  omega