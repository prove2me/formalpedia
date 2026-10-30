-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_maximal_euler_bound_552f0216_da27_4340_ada6_5c47a5b50119
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T12:25:56.502226+00:00
-- url     : https://prove2.me/submissions/9106c7ab-2944-4ee0-ba2b-81bd96e0a053

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_bound_552f0216_da27_4340_ada6_5c47a5b50119

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ H' : SimpleGraph V, H ≤ H' →
      WilliamsonShmoys.HasPlanarDrawingOn H' → H' = H) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  exact WilliamsonShmoys.planar_drawing_edge_count_bound_552f0216_da27_4340_ada6_5c47a5b50119 H hH hcard