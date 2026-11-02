-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_has_triangulated_extension__p2m_4b104b32_56a0_4b02_b537_5e9d1339dc2d_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:22:03.647203+00:00
-- url     : https://prove2.me/submissions/40833954-19b8-4a3d-b5f7-82215f718771
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_drawable_extension_maximal__p2m_3c50d639_b449_4a2f_a283_3dfd9e523102_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count__p2m_3c50d639_b449_4a2f_a283_3dfd9e523102_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) [DecidableRel P.Adj]
    (hcard : 3 ≤ Fintype.card V) (hP : HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V, ∃ hQdec : DecidableRel Q.Adj,
      (letI : DecidableRel Q.Adj := hQdec;
        P ≤ Q ∧ HasPlanarDrawingOn Q ∧
        Q.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  obtain ⟨Q, hQdec, hPQ, hQ, hmax⟩ :=
    WilliamsonShmoys.drawable_extension_maximal__p2m_3c50d639_b449_4a2f_a283_3dfd9e523102_a1
      P hP
  letI : DecidableRel Q.Adj := hQdec
  have hEdge :=
    WilliamsonShmoys.maximal_drawable_edge_count__p2m_3c50d639_b449_4a2f_a283_3dfd9e523102_a1
      Q hQ hcard hmax
  exact ⟨Q, hQdec, hPQ, hQ, hEdge⟩