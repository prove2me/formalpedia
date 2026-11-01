-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_edge_bound_from_drawing__p2m_c613d228_2a90_40f8_8150_998155f5275e_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:07:21.816566+00:00
-- url     : https://prove2.me/submissions/456bd99e-5250-4e63-8c8e-a9ecc5187aff
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph__p2m_c5eab97f_571a_4af4_85c9_353e33d2f94f_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_c5eab97f_571a_4af4_85c9_353e33d2f94f_a1
import Theorems.Thm_WilliamsonShmoys_subgraph_edge_count_monotone__p2m_c5eab97f_571a_4af4_85c9_353e33d2f94f_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_c5eab97f_571a_4af4_85c9_353e33d2f94f_a1
      H hH hcard
  have hKcount :=
    WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_c5eab97f_571a_4af4_85c9_353e33d2f94f_a1
      K hK hcard hmax
  have hmono :=
    WilliamsonShmoys.subgraph_edge_count_monotone__p2m_c5eab97f_571a_4af4_85c9_353e33d2f94f_a1
      H K hHK
  omega