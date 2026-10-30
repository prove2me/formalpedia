-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_dense_extension__p2m_dc333b6e_8abf_48c5_ac8f_62c976c7967e_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:51:31.127895+00:00
-- url     : https://prove2.me/submissions/29ed7c18-6faa-44d5-9c45-034a7af206e0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_extension__p2m_6630bfc0_6fd3_4ee5_a018_4b73345ede9f_a2
import Theorems.Thm_WilliamsonShmoys_dense_of_maximal_drawable__p2m_6630bfc0_6fd3_4ee5_a018_4b73345ede9f_a2
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn P) (hV : 3 ≤ Fintype.card V) :
    ∃ Q : SimpleGraph V, P ≤ Q ∧ HasPlanarDrawingOn Q ∧
      3 * Fintype.card V ≤ Q.edgeSet.ncard + 6 := by
  obtain ⟨Q, hPQ, hQDraw, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_extension__p2m_6630bfc0_6fd3_4ee5_a018_4b73345ede9f_a2
      P hDraw
  exact ⟨Q, hPQ, hQDraw,
    WilliamsonShmoys.dense_of_maximal_drawable__p2m_6630bfc0_6fd3_4ee5_a018_4b73345ede9f_a2
      Q hQDraw hMax hV⟩