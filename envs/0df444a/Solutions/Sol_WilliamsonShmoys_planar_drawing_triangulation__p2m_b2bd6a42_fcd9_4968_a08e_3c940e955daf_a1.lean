-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation__p2m_b2bd6a42_fcd9_4968_a08e_3c940e955daf_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:21:30.314754+00:00
-- url     : https://prove2.me/submissions/19f222e5-65b1-42a7-84f6-7f4bbdb0c4ec
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_extend_to_maximal_planar_drawing__p2m_aaf0613d_435c_4fad_8a76_ba323c101cda_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_aaf0613d_435c_4fad_8a76_ba323c101cda_a1
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      (∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v) ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hGH, hH, hmax⟩ :=
    WilliamsonShmoys.extend_to_maximal_planar_drawing__p2m_aaf0613d_435c_4fad_8a76_ba323c101cda_a1 G hG
  exact ⟨H, hGH, WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_aaf0613d_435c_4fad_8a76_ba323c101cda_a1 H hcard hH hmax⟩