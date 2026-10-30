-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_a3317d7a_4b18_491b_9aee_6f2b4185d855
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T19:52:50.507365+00:00
-- url     : https://prove2.me/submissions/2e15a4ef-9cf3-4047-abfb-8ebc3f029650

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_e5c3d806_69b9_4602_a0f9_34c482daacc9
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_e5c3d806_69b9_4602_a0f9_34c482daacc9

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z)
    (hmax : ∀ W : SimpleGraph V,
      LE.le Z W →
      WilliamsonShmoys.HasPlanarDrawingOn W →
      W = Z)
    (hV : 3 ≤ Fintype.card V) :
    Z.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.planar_edge_count_upper_bound_e5c3d806_69b9_4602_a0f9_34c482daacc9 Z hZ hV
  · exact WilliamsonShmoys.maximal_planar_edge_count_lower_bound_e5c3d806_69b9_4602_a0f9_34c482daacc9 Z hZ hmax hV