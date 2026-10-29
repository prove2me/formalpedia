-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_3fdb186f_984d_4498_b0e7_7fd2238c7ad7_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:32:21.832392+00:00
-- url     : https://prove2.me/submissions/6f8f9570-ef78-4f5b-9aad-dd8a2e8fa749
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper__p2m_abdda8c5_f5c1_4e5d_b801_c7084d469782_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_abdda8c5_f5c1_4e5d_b801_c7084d469782_a2

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hu := WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_abdda8c5_f5c1_4e5d_b801_c7084d469782_a2 H hH hV
  have hl := WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_abdda8c5_f5c1_4e5d_b801_c7084d469782_a2 H hH hmax hV
  omega