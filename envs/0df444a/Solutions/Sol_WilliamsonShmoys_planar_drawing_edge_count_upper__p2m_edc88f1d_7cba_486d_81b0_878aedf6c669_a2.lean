-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_upper__p2m_edc88f1d_7cba_486d_81b0_878aedf6c669_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:16:41.383797+00:00
-- url     : https://prove2.me/submissions/60c6413b-d8fd-4462-b881-01f4176d1bb7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_triangulated_augmentation__p2m_8e79e998_aff8_4ed4_8767_b60047b8c9f0_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hEdges, hCount⟩ :=
    WilliamsonShmoys.planar_drawing_edge_count_triangulated_augmentation__p2m_8e79e998_aff8_4ed4_8767_b60047b8c9f0_a1
      H hH hCard
  omega