-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound_for_maximal_planar_edge_count_euler_v2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T18:34:11.100181+00:00
-- url     : https://prove2.me/submissions/2338adc9-177d-438a-975a-6805428688ac

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_eq_euler

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  have hEq :=
    WilliamsonShmoys.maximal_planar_edge_count_eq_euler H hH hmax hCard
  omega