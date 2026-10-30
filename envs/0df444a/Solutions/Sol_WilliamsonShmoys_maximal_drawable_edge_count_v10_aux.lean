-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count_v10_aux
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T23:01:29.026518+00:00
-- url     : https://prove2.me/submissions/0bf2d63e-6603-42cf-a9b1-b19feec02789

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_v10
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_v10

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M <= N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N <= M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.planar_edge_count_upper_v10 M hV hM
  · exact WilliamsonShmoys.maximal_planar_edge_count_lower_v10 M hV hM hmax