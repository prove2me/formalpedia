-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_2f30e2d9_4845_4c04_a5c2_ea4608bfb1b9_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:32:19.734325+00:00
-- url     : https://prove2.me/submissions/10e8d8db-3d84-43a5-a250-738906c344a5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_7b3b301f_ddd2_4d8b_ac03_5e4e874e8368_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_7b3b301f_ddd2_4d8b_ac03_5e4e874e8368_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V,
      Set.Subset M.edgeSet N.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      N = M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.planar_drawing_edge_bound__p2m_7b3b301f_ddd2_4d8b_ac03_5e4e874e8368_a1 M hV hM
  have hLower := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_7b3b301f_ddd2_4d8b_ac03_5e4e874e8368_a1 M hV hM hmax
  omega