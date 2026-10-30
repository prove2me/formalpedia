-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_4389f167_4c7c_4d6b_b9d1_6f89e764ff11_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:44:58.780302+00:00
-- url     : https://prove2.me/submissions/74813bcc-301a-4fb8-98f7-c444604d90f0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_completion__p2m_14aa0c9f_f5a1_4cc0_8732_cecb86e5e8ad_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_exact_edge_count__p2m_14aa0c9f_f5a1_4cc0_8732_cecb86e5e8ad_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V) :
    Exists (fun K : SimpleGraph V =>
      G <= K /\ WilliamsonShmoys.HasPlanarDrawingOn K /\
      K.edgeSet.ncard + 6 = 3 * Fintype.card V) := by
  obtain ⟨K, hGK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_maximal_completion__p2m_14aa0c9f_f5a1_4cc0_8732_cecb86e5e8ad_a1
      G hG
  exact ⟨K, hGK, hK,
    WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_14aa0c9f_f5a1_4cc0_8732_cecb86e5e8ad_a1
      K hK hV hmax⟩