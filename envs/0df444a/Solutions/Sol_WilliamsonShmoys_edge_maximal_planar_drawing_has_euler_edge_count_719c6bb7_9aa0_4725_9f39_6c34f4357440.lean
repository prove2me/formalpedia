-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_drawing_has_euler_edge_count_719c6bb7_9aa0_4725_9f39_6c34f4357440
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T14:50:21.493339+00:00
-- url     : https://prove2.me/submissions/7a4b776f-6603-4da1-aab1-500d9972feed
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_41b75d1a
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound_41b75d1a

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V,
      M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.planar_drawing_edge_upper_bound_41b75d1a M hV hM
  · exact WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_41b75d1a M hV hM hmax