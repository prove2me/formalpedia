-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count_3d83e52d_d7f3_4064_9901_f4d565126921
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T00:28:57.482032+00:00
-- url     : https://prove2.me/submissions/7d7664bf-5bbe-426e-b591-90e30ad05c46

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_71955334_b5e9_40f2_bf30_231a1d4336f4
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_lower_bound_71955334_b5e9_40f2_bf30_231a1d4336f4

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hX : WilliamsonShmoys.HasPlanarDrawingOn X)
    (hmax : ∀ Y : SimpleGraph V, X ≤ Y →
      WilliamsonShmoys.HasPlanarDrawingOn Y → Y = X) :
    3 * Fintype.card V = X.edgeSet.ncard + 6 := by
  have hup := WilliamsonShmoys.planar_edge_count_upper_bound_71955334_b5e9_40f2_bf30_231a1d4336f4 X hV hX
  have hlo := WilliamsonShmoys.maximal_drawable_edge_count_lower_bound_71955334_b5e9_40f2_bf30_231a1d4336f4 X hV hX hmax
  omega