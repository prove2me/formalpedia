-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_eq_euler_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T19:28:46.317463+00:00
-- url     : https://prove2.me/submissions/b911b085-aa87-4aab-92d2-4ff3c4643f2c

import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_edge_equality

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  have hEq := WilliamsonShmoys.maximal_planar_euler_edge_equality
    H hH hmax hCard
  simpa [hEq]
