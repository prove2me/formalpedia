-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_edge_completion__p2m_f0aba619_3680_404a_84c1_4b765821e2bd_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:02:53.011378+00:00
-- url     : https://prove2.me/submissions/9c18f84b-bbb8-4c6c-ac15-c89a4da75c09
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_533c1536_70f9_4baf_8d8d_aa7e4273cff9_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_533c1536_70f9_4baf_8d8d_aa7e4273cff9_a2
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ HasPlanarDrawingOn H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hGH, hH, hle, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_533c1536_70f9_4baf_8d8d_aa7e4273cff9_a2
      G hcard hG
  refine ⟨H, hGH, hH, hle, ?_⟩
  exact WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_533c1536_70f9_4baf_8d8d_aa7e4273cff9_a2
    H hcard hH hmax