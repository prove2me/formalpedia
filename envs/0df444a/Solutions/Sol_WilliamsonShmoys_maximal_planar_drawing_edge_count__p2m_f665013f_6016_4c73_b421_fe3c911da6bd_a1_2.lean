-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_f665013f_6016_4c73_b421_fe3c911da6bd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:38:13.011119+00:00
-- url     : https://prove2.me/submissions/052ecccf-9c05-4585-b07c-fd06029244c9

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_euler_7e0405ab

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, M ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.maximal_planar_edge_count_euler_7e0405ab M hM hV hMax
