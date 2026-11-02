-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_83d9f0a5_b086_4e9a_82e5_51c146823d01_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:35:35.279315+00:00
-- url     : https://prove2.me/submissions/58f7742c-a4b5-425b-a6d2-a0772604dd78
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_drawing_supergraph__p2m_b6ef5ab1_c465_4724_83b5_1fd8c793e204_a1
import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_drawing__p2m_b6ef5ab1_c465_4724_83b5_1fd8c793e204_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hH : HasPlanarDrawingOn H) :
    letI : (G : SimpleGraph V) -> DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    Exists fun K : SimpleGraph V =>
      And (LE.le H K) (And (HasPlanarDrawingOn K)
        (Eq K.edgeFinset.card (3 * Fintype.card V - 6))) := by
  classical
  letI : (G : SimpleGraph V) -> DecidableRel G.Adj := fun G => Classical.decRel G.Adj
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_drawing_supergraph__p2m_b6ef5ab1_c465_4724_83b5_1fd8c793e204_a1 H hH
  have hcount :=
    WilliamsonShmoys.edge_count_of_maximal_planar_drawing__p2m_b6ef5ab1_c465_4724_83b5_1fd8c793e204_a1
      K hcard hK hmax
  exact ⟨K, hHK, hK, hcount⟩