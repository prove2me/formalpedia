-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_e3ce4704_f609_45f0_9a05_cff1f4f992c7_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:49:09.095291+00:00
-- url     : https://prove2.me/submissions/613c5033-f00a-49b3-b005-dd069328a10e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_extension__p2m_22c09847_b733_4661_b230_9655792a93fd_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_22c09847_b733_4661_b230_9655792a93fd_a2
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hGH, hH, hMax⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_extension__p2m_22c09847_b733_4661_b230_9655792a93fd_a2
      G hG
  exact ⟨H, hGH, hH,
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_22c09847_b733_4661_b230_9655792a93fd_a2
      H hH hV hMax⟩