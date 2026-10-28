-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_has_euler_edge_count_38271ead_fcb7_486e_b3a1_3bd65c5883ef
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T21:45:27.44303+00:00
-- url     : https://prove2.me/submissions/4604d939-fede-4fda-882a-6455c298aaea
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_from_drawing_20261027
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_from_drawing_20261027

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V,
      M ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ M) :
    (M.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  apply le_antisymm
  · exact WilliamsonShmoys.planar_drawing_edge_count_upper_from_drawing_20261027 M hM hCard
  · exact WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_from_drawing_20261027 M hM hCard hMax