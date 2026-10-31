-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_b8d35c99_ccc1_4cae_8065_458ad4737ca1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:19:41.265555+00:00
-- url     : https://prove2.me/submissions/9f7bb248-6394-4412-ada2-d57cdc174c9d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_d410bfc9_f026_41fa_b924_9663ab8f4a24_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_d410bfc9_f026_41fa_b924_9663ab8f4a24_a1
import Mathlib
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hmax : forall N : SimpleGraph V, M <= N -> HasPlanarDrawingOn N -> N = M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hup := WilliamsonShmoys.planar_edge_upper_bound__p2m_d410bfc9_f026_41fa_b924_9663ab8f4a24_a1
    M hV hM
  have hlo := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_d410bfc9_f026_41fa_b924_9663ab8f4a24_a1
    M hV hM hmax
  omega