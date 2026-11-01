-- Prove2me | solution 1 for WilliamsonShmoys.simple_planar_drawing_edge_bound__p2m_e4c5d8ab_7595_4333_b2f6_7c0fac6762c1_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:24:49.711197+00:00
-- url     : https://prove2.me/submissions/a154b183-ed4a-4fff-a4f3-f7f56397122a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_edgeFinset_card_mono_of_subgraph__p2m_602c691a_8d1a_4dfe_88c6_7f0f95c89b91_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_602c691a_8d1a_4dfe_88c6_7f0f95c89b91_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_bound__p2m_602c691a_8d1a_4dfe_88c6_7f0f95c89b91_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel G.Adj := Classical.decRel _
     G.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  rcases WilliamsonShmoys.planar_drawing_maximal_extension__p2m_602c691a_8d1a_4dfe_88c6_7f0f95c89b91_a1
      G hG with ⟨H, hGH, hH, hmax⟩
  have hmono :=
    WilliamsonShmoys.edgeFinset_card_mono_of_subgraph__p2m_602c691a_8d1a_4dfe_88c6_7f0f95c89b91_a1
      G H hGH
  have hbound :=
    WilliamsonShmoys.maximal_planar_drawing_edge_bound__p2m_602c691a_8d1a_4dfe_88c6_7f0f95c89b91_a1
      H hH hmax hcard
  omega