-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_2368bce9_0700_4bbd_ab4b_7c13a596af1d_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:21:22.328455+00:00
-- url     : https://prove2.me/submissions/76c24f05-4ac3-45e9-b818-d8746f4f73bc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension__p2m_64019286_52a7_4945_b306_7d1954508408_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_64019286_52a7_4945_b306_7d1954508408_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  classical
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_extension__p2m_64019286_52a7_4945_b306_7d1954508408_a1 H hH
  refine ⟨K, hHK, hK, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_64019286_52a7_4945_b306_7d1954508408_a1 K hV hK hmax