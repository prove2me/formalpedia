-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_535e4e7e_28ad_48ed_9188_305d88c71848_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:32:26.856861+00:00
-- url     : https://prove2.me/submissions/2a57c73a-c31a-4a92-b93a-8ebc8c9c10ab
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_56609264_6a9a_4229_a716_b7a8ddd670b3_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_56609264_6a9a_4229_a716_b7a8ddd670b3_a1
import Theorems.Thm_WilliamsonShmoys_edge_count_monotone__p2m_56609264_6a9a_4229_a716_b7a8ddd670b3_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L) :
    letI : DecidableRel L.Adj := Classical.decRel L.Adj
    L.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  letI : DecidableRel L.Adj := Classical.decRel L.Adj
  obtain ⟨H, hLH, hH, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_56609264_6a9a_4229_a716_b7a8ddd670b3_a1
      L hV hL
  have hbound :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_56609264_6a9a_4229_a716_b7a8ddd670b3_a1
      H hV hH hmax
  have hmono :=
    WilliamsonShmoys.edge_count_monotone__p2m_56609264_6a9a_4229_a716_b7a8ddd670b3_a1
      L H hLH
  omega