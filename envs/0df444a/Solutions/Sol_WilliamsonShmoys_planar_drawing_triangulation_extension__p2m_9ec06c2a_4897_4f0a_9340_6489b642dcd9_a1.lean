-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_9ec06c2a_4897_4f0a_9340_6489b642dcd9_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:12:17.689006+00:00
-- url     : https://prove2.me/submissions/3f73b1fd-e252-4b4a-bbb3-9013eed19b60
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_extension__p2m_971f615d_fe0b_4924_8df8_81bd7d133755_a1
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_edge_bound__p2m_971f615d_fe0b_4924_8df8_81bd7d133755_a1

set_option autoImplicit false

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V) :
    exists K : SimpleGraph V, G <= K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V <= K.edgeSet.ncard + 6 := by
  obtain ⟨K, hGK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_extension__p2m_971f615d_fe0b_4924_8df8_81bd7d133755_a1 G hG
  exact ⟨K, hGK, hK,
    WilliamsonShmoys.edge_maximal_planar_edge_bound__p2m_971f615d_fe0b_4924_8df8_81bd7d133755_a1 K hK hV hmax⟩