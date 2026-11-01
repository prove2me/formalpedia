-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_edge_count_supergraph__p2m_765f79d2_80fc_4ea0_854a_5bf0163b6a16_a4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:22:28.761929+00:00
-- url     : https://prove2.me/submissions/8474bc9f-00fe-46d5-8b21-ea33814c6864
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_92fbdf79_5590_491f_9884_21ba60b9e74f_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_92fbdf79_5590_491f_9884_21ba60b9e74f_a1

set_option autoImplicit false

open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hGH, hH, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_92fbdf79_5590_491f_9884_21ba60b9e74f_a1 G hG
  have hcount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_92fbdf79_5590_491f_9884_21ba60b9e74f_a1 H hcard hH hmax
  exact ⟨H, hGH, hH, hcount⟩