-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_abcc1e5a_cabd_49d6_8da8_bf017a643b84_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:32:56.896207+00:00
-- url     : https://prove2.me/submissions/6c81019b-cfd9-4410-aa52-7e9c66f426b7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_acd844a2_f18b_4cf8_8cd2_2591d79fbd14_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_acd844a2_f18b_4cf8_8cd2_2591d79fbd14_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hLH, hmono, hH, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_acd844a2_f18b_4cf8_8cd2_2591d79fbd14_a1
      L hL
  have hbound :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_acd844a2_f18b_4cf8_8cd2_2591d79fbd14_a1
      H hcard hH hmax
  omega